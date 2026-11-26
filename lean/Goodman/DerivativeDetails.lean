-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.DiskDerivative
public import Goodman.SlitPositivity

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

/-- The centered function H of Lemma 8, in the finite target coordinate. -/
def centeredPullback (G : ℂ → Sphere) (φ : ℂ → ℂ) (U : Set Sphere) (w z : ℂ) : ℂ :=
  (finitePart (G (φ z)) - w) / (radius U w : ℂ)

variable {Ω : Set ℂ} {U : Set Sphere} {G : ℂ → Sphere} {φ : ℂ → ℂ} {a w : ℂ}

private theorem affine_coeff_complex (G : ℂ → Sphere) (a w r t : ℂ) {n : ℕ} (hn : 0 < n) :
    coeff n (fun z => (finitePart (G (a + r * z)) - w) / t) =
      r ^ n * iteratedDeriv n (finitePart ∘ G) a / ((n.factorial : ℂ) * t) := by
  let f (z : ℂ) := (-w + (finitePart ∘ G) (a + z)) / t
  have he : (fun z => (finitePart (G (a + r * z)) - w) / t) = fun z => f (r * z) := by
    funext z
    simp [f, sub_eq_add_neg, add_comm]
  rw [he, coeff_comp_mul_left]
  simp only [f, coeff, iteratedDeriv_div_const, iteratedDeriv_const_add hn,
    iteratedDeriv_comp_const_add, add_zero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem pullback_affine_germ {σ : ℂ → ℂ} {r : ℂ}
    (he : φ ∘ σ =ᶠ[𝓝 0] fun z => a + r * z) :
    centeredPullback G φ U w ∘ σ =ᶠ[𝓝 0]
      fun z => (finitePart (G (a + r * z)) - w) / (radius U w : ℂ) :=
  he.fun_comp (fun y => (finitePart (G y) - w) / (radius U w : ℂ))

private theorem restore_pullback_germ {σ : ℂ → ℂ} {r : ℂ} (c : CenteredChart U w)
    (hG : SphereHolomorphicOn G Ω) (ha : a ∈ Ω) (hw : G a = (w : Sphere))
    (he : φ ∘ σ =ᶠ[𝓝 0] fun z => a + r * z) :
    (fun z => G (a + r * z)) =ᶠ[𝓝 0]
      fun z => ((w + (radius U w : ℂ) * centeredPullback G φ U w (σ z) : ℂ) : Sphere) := by
  have ht : Tendsto (fun z : ℂ => a + r * z) (𝓝 0) (𝓝 a) := by
    have h : ContinuousAt (fun z : ℂ => a + r * z) 0 := by fun_prop
    simpa using h.tendsto
  have hfin := (hG.affine_germ ha (hw ▸ OnePoint.coe_ne_infty w)).2
  have hrad := Complex.ofReal_ne_zero.mpr c.radius_pos.ne'
  filter_upwards [ht.eventually hfin, pullback_affine_germ (G := G) (U := U) (w := w) he]
    with z hz hH
  rw [hz, ← Function.comp_apply (f := centeredPullback G φ U w) (g := σ), hH,
    mul_div_cancel₀ _ hrad, add_sub_cancel]

/-- The affine disk germ, with the finite value restored in the spherical target. -/
theorem disk_centered_germ (c : CenteredChart U w) (ha : a ∈ disk)
    (hG : SphereHolomorphicOn G disk) (hw : G a = (w : Sphere)) :
    (fun z => G (a + (radius (planeDomain disk) a : ℂ) * z)) =ᶠ[𝓝 0]
      fun z => ((w + (radius U w : ℂ) *
        centeredPullback G (diskForward a) U w (diskKernel (star a) z) : ℂ) : Sphere) := by
  rw [radius_planeDomain_disk ha]
  exact restore_pullback_germ c hG ha hw (diskForward_kernel_germ a)

/-- The complex disk derivative identity. The summation index j represents degree j+1 of H. -/
theorem disk_derivative_sum (ha : a ∈ disk) (hG : SphereHolomorphicOn G disk)
    (hw : G a = (w : Sphere)) {n : ℕ} (hn : 0 < n) :
    (radius (planeDomain disk) a : ℂ) ^ n * iteratedDeriv n (finitePart ∘ G) a /
        ((n.factorial : ℂ) * (radius U w : ℂ)) =
      ∑ j ∈ Finset.range n, ((n-1).choose j : ℂ) * star a ^ (n-1-j) *
        coeff (j+1) (centeredPullback G (diskForward a) U w) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hg := (hG.affine_germ ha (hw ▸ OnePoint.coe_ne_infty w)).1
  have hf := hg.comp_of_eq ((diskForward_bihol ha).1 0 (by simp [disk])) (diskForward_zero a)
  have hH : AnalyticAt ℂ (centeredPullback G (diskForward a) U w) 0 :=
    (hf.sub analyticAt_const).div_const
  rw [radius_planeDomain_disk ha, ← affine_coeff_complex G a w _ _ hn,
    ← coeff_congr_of_eventuallyEq (pullback_affine_germ (diskForward_kernel_germ a)),
    coeff_comp_diskKernel hH, Nat.succ_sub_one]

/-- Coefficient estimates only through the requested order suffice for Theorem 3(a). -/
theorem disk_derivative_of_first_coeffs (ha : a ∈ disk) (hG : SphereHolomorphicOn G disk)
    (hw : G a = (w : Sphere)) {n : ℕ} (hn : 0 < n)
    (hb : ∀ k, 1 ≤ k → k ≤ n →
      ‖coeff k (centeredPullback G (diskForward a) U w)‖ ≤ A (poleParam U w) k) :
    derivativeRatio n G a (radius (planeDomain disk) a) (radius U w) ≤
      D (poleParam U w) ‖a‖ n := by
  have ht : 0 ≤ radius U w := by unfold radius; split <;> positivity
  have hr : 0 ≤ radius (planeDomain disk) a := (radius_planeDomain_disk ha) ▸ (diskRadius_pos ha).le
  have he := congrArg norm (disk_derivative_sum (U := U) ha hG hw hn)
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_of_nonneg hr, Complex.norm_of_nonneg ht] at he
  rw [derivativeRatio, he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul, norm_pow, norm_star, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hb (j+1) (Nat.succ_pos _) (Finset.mem_range.mp hj)) (by positivity)

/-- The positive-derivative chart of Lemma 8 gives a normalized convex univalent
source. Its inverse on the disk image is analytic and two-sided near zero. -/
theorem convex_source_normalize (hc : Convex ℝ Ω) (hφ : Bihol disk Ω φ)
    (hφ0 : φ 0 = a) (hd : deriv φ 0 = (radius (planeDomain Ω) a : ℂ)) :
    let s := fun z => (φ z - a) / (radius (planeDomain Ω) a : ℂ)
    let σ := Function.invFunOn s disk
    IsS s ∧ Convex ℝ (s '' disk) ∧ σ 0 = 0 ∧ AnalyticAt ℂ σ 0 ∧
      σ ∘ s =ᶠ[𝓝 0] id ∧ s ∘ σ =ᶠ[𝓝 0] id := by
  classical
  intro s σ
  obtain ⟨hφa, χ, hχ, hm, hi, hl, hr⟩ := hφ
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hD : disk ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds hzero
  have hleft := hl.eqOn.eventuallyEq_of_mem hD
  have hprod : deriv χ (φ 0) * deriv φ 0 = 1 := by
    rw [← deriv_comp 0 (hχ _ (hm hzero)).differentiableAt (hφa _ hzero).differentiableAt,
      hleft.deriv_eq, deriv_id]
  have hne : (radius (planeDomain Ω) a : ℂ) ≠ 0 := by
    intro h
    simp [hd, h] at hprod
  have hs : IsS s := by
    refine ⟨fun z hz => ((hφa z hz).sub analyticAt_const).div_const, ?_, ?_, ?_⟩
    · intro y hy z hz he
      exact hl.injOn hy hz (sub_left_inj.mp ((div_left_inj' hne).mp he))
    · simp [s, hφ0]
    · dsimp only [s]
      rw [deriv_div_const, deriv_sub_const, hd, div_self hne]
  have hconv : Convex ℝ (s '' disk) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ u v hu hv huv
    have hmem := hc (hm hy) (hm hz) hu hv huv
    refine ⟨χ _, hi hmem, ?_⟩
    dsimp only [s]
    rw [hr hmem]
    simp only [Complex.real_smul]
    have huv' : (u : ℂ) + v = 1 := by exact_mod_cast huv
    field_simp [hne]
    linear_combination a * huv'
  have hls : LeftInvOn σ s disk := hs.2.1.leftInvOn_invFunOn
  have hlocal : σ ∘ s =ᶠ[𝓝 0] id := hls.eqOn.eventuallyEq_of_mem hD
  have hs0 := hs.2.2.1
  have hs1 := hs.2.2.2.trans_ne one_ne_zero
  have hsa := hs.1 0 hzero
  refine ⟨hs, hconv, by simpa only [hs0] using hls hzero, ?_, hlocal, ?_⟩
  · rw [← hs0]
    exact (analyticAt_comp_iff_of_deriv_ne_zero hsa hs1).mp (analyticAt_id.congr hlocal.symm)
  · rw [← hs0, ← hsa.hasStrictDerivAt.map_nhds_eq hs1]
    change ∀ᶠ z in map s (𝓝 0), s (σ z) = z
    exact eventually_map.mpr (hlocal.mono fun z hz => congrArg s hz)

/-- The affine germ on a convex source and the complex coefficient read from it
using the actual local inverse of the normalized chart. -/
theorem convex_centered_germ (c : CenteredChart U w) (hc : Convex ℝ Ω)
    (hφ : Bihol disk Ω φ) (hφ0 : φ 0 = a) (hd : deriv φ 0 = (radius (planeDomain Ω) a : ℂ))
    (hG : SphereHolomorphicOn G Ω) (hw : G a = (w : Sphere)) :
    let r : ℂ := radius (planeDomain Ω) a
    let s := fun z => (φ z - a) / r
    let σ := Function.invFunOn s disk
    let H := centeredPullback G φ U w
    ((fun z => G (a + r*z)) =ᶠ[𝓝 0] fun z => ((w + (radius U w : ℂ) * H (σ z) : ℂ) : Sphere)) ∧
      ∀ n : ℕ, 0 < n → coeff n (H ∘ σ) =
        r ^ n * iteratedDeriv n (finitePart ∘ G) a / ((n.factorial : ℂ) * (radius U w : ℂ)) := by
  intro r s σ H
  obtain ⟨hs, _, _, _, _, hright⟩ := convex_source_normalize hc hφ hφ0 hd
  have hr : r ≠ 0 := by
    intro he
    have h := hs.2.2.2
    change deriv (fun z => (φ z - a) / r) 0 = 1 at h
    simp [he] at h
  have he : φ ∘ σ =ᶠ[𝓝 0] fun z => a + r*z := by
    filter_upwards [hright] with z hz
    change (φ (σ z) - a) / r = z at hz
    change φ (σ z) = a + r*z
    exact (sub_eq_iff_eq_add.mp ((div_eq_iff hr).mp hz)).trans (by ring)
  have ha : a ∈ Ω := hφ0 ▸ hφ.2.choose_spec.2.1 (by simp [disk] : (0 : ℂ) ∈ disk)
  exact ⟨restore_pullback_germ c hG ha hw he, fun n hn =>
    (coeff_congr_of_eventuallyEq (pullback_affine_germ he) n).trans (affine_coeff_complex G a w _ _ hn)⟩

/-- At degree n-1 the top monomial vanishes. Each lower monomial shifts the
coefficient of H' v^j down to degree n-j-1. -/
theorem convex_top_coeff {H v : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (hv : AnalyticAt ℂ v 0)
    {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    coeff (n-1) (fun z => deriv H z * z^j * v z^j) =
      if j = n then 0 else coeff (n-j-1) (fun z => deriv H z * v z^j) := by
  rw [show (fun z => deriv H z * z^j * v z^j) =
      fun z => z^j * (deriv H z * v z^j) by funext z; ring]
  have hm (i : ℕ) : coeff i (fun z : ℂ => z^j) = if i = j then 1 else 0 := by
    rw [coeff, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst i; simp [Nat.cast_ne_zero.mpr j.factorial_ne_zero]
    · simp
  rw [coeff_mul (f := fun z => z^j) (analyticAt_id.fun_pow _) (hH.deriv.fun_mul (hv.fun_pow _))]
  by_cases he : j = n
  · subst j
    simp [hm, ite_mul, Finset.sum_ite_eq', show ¬ n < n-1+1 by omega]
  · simp [hm, he, ite_mul, Finset.sum_ite_eq', show j < n-1+1 by omega,
      show n-1-j = n-j-1 by omega]

/-- The Fejér derivative factor k=n-j cancels the Lagrange denominator n. -/
theorem convex_binomial_factor {j n : ℕ} (hj : j < n) :
    ((n-j : ℕ) : ℝ) * n.choose j / n = ((n-1).choose (n-j-1) : ℝ) := by
  have he := Nat.add_one_mul_choose_eq (n-1) (n-j-1)
  rw [show n-1+1 = n by omega, show n-j-1+1 = n-j by omega,
    Nat.choose_symm hj.le] at he
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using he.symm :
    (n-j) * n.choose j = (n-1).choose (n-j-1) * n)

/-- Reindexing the surviving terms by k=n-j gives exactly D_n(p,1). -/
theorem convex_binomial_sum (p : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (((n-j : ℕ) : ℝ) * n.choose j / n) * A p (n-j)) = D p 1 n := by
  unfold D
  simp only [one_pow, mul_one]
  rw [← Finset.sum_range_reflect (fun i => ((n-1).choose i : ℝ) * A p (i+1)) n]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [convex_binomial_factor hj', show n-1-j = n-j-1 by omega, show n-j-1+1 = n-j by omega]

#print axioms disk_centered_germ
#print axioms disk_derivative_sum
#print axioms disk_derivative_of_first_coeffs
#print axioms convex_source_normalize
#print axioms convex_centered_germ
#print axioms convex_top_coeff
#print axioms convex_binomial_factor
#print axioms convex_binomial_sum

end Goodman
