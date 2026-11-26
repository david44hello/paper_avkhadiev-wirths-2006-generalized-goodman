-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.CoefficientClaims

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman
namespace MainReduction

private theorem finite_recip (z : ℂ) : finitePart (fromRecip z) = z⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp [fromRecip, finitePart, OnePoint.infty]
  · simp [fromRecip, hz, finitePart]
    rfl

theorem finite_germ {f : ℂ → Sphere} {U : Set ℂ} {x : ℂ}
    (hf : SphereHolomorphicOn f U) (hx : x ∈ U) (hval : f x ≠ OnePoint.infty) :
    AnalyticAt ℂ (finitePart ∘ f) x := by
  obtain ⟨g, hg, ha | hb⟩ := hf x hx
  · apply hg.congr
    filter_upwards [ha] with z hz
    rw [Function.comp_apply, hz]
    rfl
  · have hne : g x ≠ 0 := by
      intro h
      apply hval
      simpa [fromRecip, h] using hb.self_of_nhds
    apply (hg.inv hne).congr
    filter_upwards [hb] with z hz
    simp only [Function.comp_apply, hz, finite_recip, Pi.inv_apply]

/-- The transfer keeps the precise deficit factor, including the derivative of the inner map. -/
theorem weighted_deficit (transfer : TransferClaim) (deficit : DeficitClaim)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ} (hq : IsSlitMap p q)
    {f : ℂ → Sphere} (hf : IsM p f) {h e : ℂ → ℂ} (hh : IsSchwarz h) (he : IsWeight e)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤
    A p n - slitR p * (coeff n q).re * (1 - ‖e 0 * (deriv h 0)^n‖) := by
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have f0 : f 0 ≠ OnePoint.infty := hf.2.2.2.2.1 ▸ OnePoint.coe_ne_infty (0 : ℂ)
  obtain ⟨E, hE, hE0, htransfer⟩ := transfer h hh e he n
  change ‖coeff n (fun z => e z * (finitePart ∘ f) (h z))‖ ≤ _
  rw [htransfer (finitePart ∘ f) (finite_germ hf.1 h0 f0), ← hE0]
  exact deficit p hp hp1 q hq f hf E hE n hn

theorem derivative_norm_one_of_equality (transfer : TransferClaim) (slit : SlitClaim)
    (deficit : DeficitClaim) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h)
    {n : ℕ} (hn : 1 ≤ n) (heq : ‖coeff n (fun z => finitePart (f (h z)))‖ = A p n) :
    ‖deriv h 0‖ = 1 := by
  obtain ⟨q, hq, hpos, _⟩ := slit p hp hp1
  have hone : IsWeight (fun _ => 1) := ⟨fun _ _ => analyticAt_const, by simp⟩
  have hle := weighted_deficit transfer deficit hp hp1 hq hf hh hone hn
  simp only [one_mul, norm_pow, heq] at hle
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  obtain ⟨E, hE, hE0, _⟩ := transfer h hh _ hone n
  have hnorm := hE.2 0 h0
  rw [hE0, one_mul, norm_pow] at hnorm
  have hr : 0 < slitR p := by unfold slitR; positivity
  have hfactor := mul_pos hr (hpos n hn).2
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : n ≠ 0)).mp
  exact le_antisymm hnorm (by_contra fun hlt =>
    (not_lt_of_ge (by linarith : 0 ≥ slitR p * (coeff n q).re * (1 - ‖deriv h 0‖ ^ n)))
      (mul_pos hfactor (sub_pos.mpr (lt_of_not_ge hlt))))

theorem weighted_of_transfer_slit_deficit (transfer : TransferClaim) (slit : SlitClaim)
    (deficit : DeficitClaim) : WeightedBound := by
  intro p hp hp1 f hf h hh e he n hn
  obtain ⟨q, hq, hpos, _⟩ := slit p hp hp1
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have f0 : f 0 ≠ OnePoint.infty := hf.2.2.2.2.1 ▸ OnePoint.coe_ne_infty (0 : ℂ)
  obtain ⟨E, hE, _, htransfer⟩ := transfer h hh e he n
  change ‖coeff n (fun z => e z * (finitePart ∘ f) (h z))‖ ≤ _
  rw [htransfer (finitePart ∘ f) (finite_germ hf.1 h0 f0)]
  have hR : 0 ≤ slitR p := by unfold slitR; positivity
  have hmargin := mul_nonneg (mul_nonneg hR (hpos n hn).2.le) (sub_nonneg.mpr (hE.2 0 h0))
  exact (deficit p hp hp1 q hq f hf E hE n hn).trans (sub_le_self _ hmargin)

end MainReduction
end Goodman
