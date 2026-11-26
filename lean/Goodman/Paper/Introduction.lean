-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Paper.Corollaries
import Goodman.Paper.Centered

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

private theorem zero_in_D : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one

private theorem id_schwarz : IsSchwarz id := ⟨fun _ _ => analyticAt_id, mapsTo_id _,rfl⟩

theorem IsM.composition_holomorphic {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    {h : ℂ → ℂ} (hh : IsSchwarz h) : SphereHolomorphicOn (f ∘ h) disk :=
  hf.1.comp_analyticOnNhd hh.1 hh.2.1

/-- Infinity is taken exactly above the pole, and those preimages are isolated. -/
theorem IsM.composition_poles {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere}
    (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {x : ℂ} (hx : x ∈ disk) :
    (f (h x) = OnePoint.infty ↔ h x = p) ∧
    (∀ᶠ z in 𝓝[≠] x, f (h z) ≠ OnePoint.infty) := by
  have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
  have hit (z : ℂ) (hz : z ∈ disk) : f (h z) = OnePoint.infty ↔ h z = p :=
    ⟨fun he => hf.2.1 (hh.2.1 hz) hpD (he.trans hf.2.2.1.symm), fun he => he ▸ hf.2.2.1⟩
  refine ⟨hit x hx,?_⟩
  have ho := (hh.1 x hx).eventually_eq_or_eventually_ne (analyticAt_const (v:=(p:ℂ)))
  rcases ho with he|hne
  · have hglob : EqOn h (fun _ => (p:ℂ)) disk :=
      hh.1.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
        (convex_ball (0:ℂ) (1:ℝ)).isPreconnected hx he
    have hbad := hglob zero_in_D
    rw [hh.2.2] at hbad
    change (0 : ℂ) = (p : ℂ) at hbad
    exact (hp.ne (by exact_mod_cast hbad : 0 = p)).elim
  · have hD : ∀ᶠ z in 𝓝[≠] x, z ∈ disk := mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hx)
    filter_upwards [hne,hD] with z hn hz
    exact fun hInf => hn ((hit z hz).mp hInf)

theorem IsM.taylor_in_inner_disk {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {z : ℂ} (hz : ‖z‖ < p) :
    HasSum (fun n : ℕ => coeff n (fun t => finitePart (f (h t))) * z^n) (finitePart (f (h z))) := by
  let g := fun t => finitePart (f (h t))
  have hd : DifferentiableOn ℂ g (ball 0 p) := fun t ht =>
    (hf.finite_comp_of_norm_lt hp hp1 hh (mem_ball_zero_iff.mp ht)).2.differentiableAt.differentiableWithinAt
  simpa [g,coeff,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
    Complex.hasSum_taylorSeries_on_ball hd (mem_ball_zero_iff.mpr hz)

theorem IsM.normalized_coefficients {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    coeff 0 (finitePart ∘ f) = 0 ∧ coeff 1 (finitePart ∘ f) = 1 := by
  constructor
  · simp [coeff, hf.2.2.2.2.1,finitePart]
    rfl
  · simp [coeff,hf.hasDerivAt_zero.deriv]

theorem noninjective_composition_example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsM p (extremal p) ∧ IsSchwarz (fun _ : ℂ => 0) ∧
    ¬ InjOn (extremal p ∘ (fun _ : ℂ => (0:ℂ))) disk := by
  refine ⟨isM_extremal hp hp1, ⟨fun _ _ => analyticAt_const,fun _ _ => zero_in_D,rfl⟩, ?_⟩
  intro hi
  have hhalf : (1/2 : ℂ) ∈ disk := by norm_num [disk,norm_div]
  have := hi zero_in_D hhalf rfl
  norm_num at this

theorem unweighted_goodman (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => finitePart (f (h z)))‖ ≤ A p n := by
  simpa using theorem_one_bound H1 p hp hp1 f hf h hh (fun _ => 1)
    ⟨fun _ _ => analyticAt_const,by simp⟩ n hn

theorem base_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    {n : ℕ} (hn : 2 ≤ n) : ‖coeff n (finitePart ∘ f)‖ = A p n ↔ EqOn f (extremal p) disk := by
  have hi : IsRotation id := ⟨1,by simp,fun _ _ => by simp⟩
  simpa [Function.comp_def,hi] using theorem_one_higher_equality H1 H2 p hp hp1 f hf id id_schwarz n hn

theorem rogosinski_weighted (H1 : Robertson) {F h e : ℂ → ℂ} (hF : IsS F)
    (hh : IsSchwarz h) (he : IsWeight e) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => e z * F (h z))‖ ≤ (n : ℝ) :=
  planar_weighted_comp transfer (product_of_robertson H1) hF hh he hn

end Goodman
