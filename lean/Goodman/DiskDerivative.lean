-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.UniformizationProof
public import Goodman.ChartInvariance
public import Goodman.CoefficientComposition
public import Goodman.Extremal

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

theorem disk_isSource : IsSource disk := by
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  let _ : ContractibleSpace disk := (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, h0⟩
  refine ⟨isOpen_ball, inferInstanceAs (SimplyConnectedSpace disk), ?_⟩
  exact (ne_univ_iff_exists_notMem _).mpr ⟨1, by simp [disk]⟩

/-- Disk parametrization with positive real derivative at zero. -/
def diskForward (a z : ℂ) : ℂ := (a + z) / (1 + star a * z)

theorem diskForward_bihol {a : ℂ} (ha : a ∈ disk) : Bihol disk disk (diskForward a) := by
  have hn : -a ∈ disk := by simpa [disk, mem_ball_zero_iff] using ha
  have he : diskForward a = diskInverse (-a) := by
    funext z
    simp [diskForward, diskInverse, add_comm a]
  rw [he]
  exact diskInverse_bihol hn

@[simp] theorem diskForward_zero (a : ℂ) : diskForward a 0 = a := by simp [diskForward]

theorem deriv_diskForward (a : ℂ) :
    deriv (diskForward a) 0 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
  have h := (((hasDerivAt_const (0 : ℂ) a).add (hasDerivAt_id 0)).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id 0).const_mul (star a)))
    (by simp)).deriv
  change deriv (diskForward a) 0 = _ at h
  rw [h]
  simp [← Complex.mul_conj']

/-- The plane chart supplied by a biholomorphic parametrization computes its conformal radius. -/
theorem radius_planeDomain_of_bihol {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : Bihol disk Ω φ) :
    radius (planeDomain Ω) (φ 0) = ‖deriv φ 0‖ := by
  obtain ⟨hφa, χ, hχ, hm, hi, hl, hr⟩ := hφ
  let c : CenteredChart (planeDomain Ω) (φ 0) := {
    forward := fun z => (φ z : Sphere)
    inverse := χ ∘ finitePart
    forward_holo := fun z hz => ⟨φ, hφa z hz, Or.inl (Eventually.of_forall fun _ => rfl)⟩
    inverse_holo := ⟨fun z hz => hχ z (by simpa [planeDomain] using hz),
      fun h => by simp [planeDomain] at h⟩
    forward_maps := fun z hz => ⟨φ z, hm hz, rfl⟩
    inverse_maps := by rintro _ ⟨z, hz, rfl⟩; exact hi hz
    left_inverse := hl
    right_inverse := by rintro _ ⟨z, hz, rfl⟩; exact congrArg OnePoint.some (hr hz)
    center := rfl }
  exact c.radius_eq

theorem diskRadius_pos {a : ℂ} (ha : a ∈ disk) : 0 < 1 - ‖a‖ ^ 2 := by
  have h := mem_ball_zero_iff.mp ha
  nlinarith [sq_lt_sq₀ (norm_nonneg a) zero_le_one |>.2 h]

theorem radius_planeDomain_disk {a : ℂ} (ha : a ∈ disk) :
    radius (planeDomain disk) a = 1 - ‖a‖ ^ 2 := by
  have h := radius_planeDomain_of_bihol (diskForward_bihol ha)
  rwa [diskForward_zero, deriv_diskForward, Complex.norm_of_nonneg (diskRadius_pos ha).le] at h

/-- The inverse chart in the affine source variable centered at `a`. -/
def diskKernel (b z : ℂ) : ℂ := z / (1 - b * z)

private theorem diskScale_ne {a : ℂ} (ha : a ∈ disk) : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (diskRadius_pos ha).ne'

theorem diskInverse_affine {a : ℂ} (ha : a ∈ disk) (z : ℂ) :
    diskInverse a (a + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * z) = diskKernel (star a) z := by
  let c : ℂ := ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)
  have hc : c ≠ 0 := diskScale_ne ha
  have h : (star a) * a = 1 - c := by simp [c, ← Complex.conj_mul']
  change (a + c * z - a) / (1 - star a * (a + c * z)) = _
  rw [add_sub_cancel_left, mul_add, h, show 1 - (1 - c + star a * (c * z)) =
    c * (1 - star a * z) by ring]
  exact mul_div_mul_left _ _ hc

theorem diskKernel_analyticAt (b : ℂ) : AnalyticAt ℂ (diskKernel b) 0 :=
  analyticAt_id.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)

theorem diskForward_kernel_germ (a : ℂ) :
    (diskForward a ∘ diskKernel (star a)) =ᶠ[𝓝 0]
      fun z => a + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * z := by
  have h : ContinuousAt (fun z : ℂ => 1 - star a * z) 0 := by fun_prop
  filter_upwards [h.eventually_ne (by simp : 1 - star a * (0 : ℂ) ≠ 0)] with z hz
  have hd : 1 + star a * (z / (1 - star a * z)) = (1 - star a * z)⁻¹ := by
    field_simp [hz]
    ring
  change (a + z / (1 - star a * z)) / (1 + star a * (z / (1 - star a * z))) = _
  rw [hd, div_inv_eq_mul, add_mul, div_mul_cancel₀ _ hz]
  have hnorm : ((‖a‖ : ℂ) ^ 2) = a * star a := (Complex.mul_conj' a).symm
  push_cast
  rw [hnorm]
  ring

/-- The positive-degree Taylor coefficients of a power of the inverse chart. -/
theorem coeff_diskKernel_pow (b : ℂ) {m j : ℕ} (hj : j ≤ m) :
    coeff (m + 1) (fun z => diskKernel b z ^ (j + 1)) =
      (m.choose j : ℂ) * b ^ (m-j) := by
  let α (n : ℕ) : ℂ := if j + 1 ≤ n then ((n-1).choose j : ℂ) * b ^ (n-(j+1)) else 0
  have hc (n : ℕ) : coeff n (fun z => diskKernel b z ^ (j+1)) = α n := by
    apply coeff_of_eventually_hasSum
    have h : ContinuousAt (fun z : ℂ => ‖b * z‖) 0 := by fun_prop
    filter_upwards [h.eventually_lt continuousAt_const (by simp : ‖b * (0 : ℂ)‖ < 1)] with z hz
    apply (hasSum_nat_add_iff' (j+1)).mp
    have hzero : ∑ i ∈ Finset.range (j+1), z ^ i * α i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [α, ite_eq_right (not_le.mpr (Finset.mem_range.mp hi)), mul_zero]
    rw [hzero, sub_zero]
    convert ((hasSum_choose_mul_geometric_of_norm_lt_one j hz).mul_left (z ^ (j+1))).congr_fun
      (g := fun n => z ^ (n + (j+1)) * α (n + (j+1))) ?_ using 1
    · simp only [diskKernel, div_eq_mul_inv, mul_pow, inv_pow, one_mul]
    · intro n
      simp only [α, ite_eq_left (show j+1 ≤ n+(j+1) by omega),
        show n+(j+1)-1 = n+j by omega, Nat.add_sub_cancel, pow_add, mul_pow]
      ring
  simpa [α, hj] using hc (m+1)

/-- Finite coefficient formula at every positive derivative order. -/
theorem coeff_comp_diskKernel {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (b : ℂ) (m : ℕ) :
    coeff (m+1) (F ∘ diskKernel b) =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℂ) * b ^ (m-j) * coeff (j+1) F := by
  rw [coeff_comp_finite hF (diskKernel_analyticAt b) (by simp [diskKernel]), Finset.sum_range_succ']
  have hconst : coeff (m+1) (fun _ : ℂ => (1 : ℂ)) = 0 := by simp [coeff, iteratedDeriv_const]
  simp only [pow_zero, hconst, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_diskKernel_pow b (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), mul_comm]

/-- The derivative ratio is the norm of a coefficient in the normalized affine variable. -/
theorem derivativeRatio_eq_affine_coeff (G : ℂ → Sphere) (a w : ℂ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (n : ℕ) (hn : 0 < n) :
    derivativeRatio n G a s t =
      ‖coeff n (fun z => (finitePart (G (a + (s : ℂ) * z)) - w) / (t : ℂ))‖ := by
  let g := finitePart ∘ G
  let f (z : ℂ) := (-w + g (a + z)) / (t : ℂ)
  have he : (fun z => (finitePart (G (a + (s : ℂ) * z)) - w) / (t : ℂ)) =
      (fun z => f (s * z)) := by funext z; simp [f, g, sub_eq_add_neg, add_comm]
  rw [he, coeff_comp_mul_left, norm_mul, norm_pow, Complex.norm_of_nonneg hs]
  simp only [f, coeff, iteratedDeriv_div_const, iteratedDeriv_const_add hn,
    iteratedDeriv_comp_const_add, add_zero, norm_div, Complex.norm_natCast,
    Complex.norm_of_nonneg ht, derivativeRatio, g]
  ring

/-- Theorem 3(a) follows by centering with the disk automorphism and summing the binomial kernel. -/
theorem diskDerivativeBound_of_centeredClaim (h : CenteredClaim) : DiskDerivativeBound := by
  intro U a w hU ha G hG hm hcenter n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let F (z : ℂ) := (finitePart (G (diskForward a z)) - w) / (radius U w : ℂ)
  have hφ := diskForward_bihol ha
  have hder : deriv (diskForward a) 0 = (radius (planeDomain disk) a : ℂ) := by
    rw [radius_planeDomain_disk ha, deriv_diskForward]
  have hbound (j : ℕ) : ‖coeff (j+1) F‖ ≤ A (poleParam U w) (j+1) := by
    have hb := h disk U a w disk_isSource ha hU G hG hm hcenter (diskForward a) hφ
      (diskForward_zero a) hder (fun _ => 1)
      ⟨analyticOnNhd_const, fun _ _ => by simp⟩ (j+1) (by omega)
    simpa [F] using hb
  have hg := (hG.affine_germ ha (hcenter ▸ OnePoint.coe_ne_infty w)).1
  have hf0 := hg.comp_of_eq (hφ.1 0 (by simp [disk])) (diskForward_zero a)
  have hf : AnalyticAt ℂ F 0 := (hf0.sub analyticAt_const).div_const
  have hrad : 0 ≤ radius U w := by
    unfold radius
    split <;> positivity
  rw [radius_planeDomain_disk ha, derivativeRatio_eq_affine_coeff G a w (diskRadius_pos ha).le
    hrad _ (by omega)]
  have he : (F ∘ diskKernel (star a)) =ᶠ[𝓝 0] fun z =>
      (finitePart (G (a + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * z)) - w) / (radius U w : ℂ) := by
    filter_upwards [diskForward_kernel_germ a] with z hz
    exact congrArg (fun u => (finitePart (G u) - w) / (radius U w : ℂ)) hz
  rw [← coeff_congr_of_eventuallyEq he, coeff_comp_diskKernel hf]
  apply (norm_sum_le _ _).trans
  unfold D
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul, norm_pow, norm_star, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hbound j) (by positivity)

/--
info: 'Goodman.diskDerivativeBound_of_centeredClaim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diskDerivativeBound_of_centeredClaim

end Goodman
