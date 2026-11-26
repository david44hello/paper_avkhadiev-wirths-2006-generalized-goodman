-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.UnweightedTransfer
public import Goodman.Paper.Introduction
public import Goodman.Paper.BaseReduction
public import Goodman.SlitPullback

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem unweighted_cayley_properties {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ} (ht : ‖t‖ = 1) :
    let C := fun z : ℂ => (1+t*h z)/(1-t*h z)
    AnalyticOnNhd ℂ C disk ∧ C 0 = 1 ∧ ∀ z ∈ disk, 0 < (C z).re := by
  refine ⟨fun z hz => ?_, by simp [hh.2.2], fun z hz => szapiel_re_pos hh ht hz⟩
  have hholo := (analyticAt_const (v:=t)).mul (hh.1 z hz)
  apply (analyticAt_const.add hholo).div (analyticAt_const.sub hholo)
  apply sub_ne_zero.mpr
  intro h
  have hnorm := mem_ball_zero_iff.mp (hh.2.1 hz)
  have heq := congrArg norm h
  simp [norm_mul,ht] at heq
  linarith

theorem disk_origin_hyperbolic_distance {z : ℂ} (hz : z ∈ disk) :
    hypDistanceFrom (planeDomain disk) 0 (z : Sphere) = Real.artanh ‖z‖ := by
  let c : CenteredChart (planeDomain disk) 0 := {
    forward := fun t => (t : Sphere)
    inverse := finitePart
    forward_holo := fun x _ => ⟨id, analyticAt_id,Or.inl (Eventually.of_forall fun _ => rfl)⟩
    inverse_holo := ⟨fun _ _ => analyticAt_id,fun hi => by simp [planeDomain] at hi⟩
    forward_maps := fun x hx => ⟨x,hx,rfl⟩
    inverse_maps := by rintro _ ⟨y,hy,rfl⟩; exact hy
    left_inverse := fun _ _ => rfl
    right_inverse := by rintro _ ⟨y,hy,rfl⟩; rfl
    center := rfl }
  exact c.hypDistanceFrom_eq ⟨z,hz,rfl⟩

theorem slit_second_from_robertson (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {F : ℂ → ℂ} (hF : IsS F)
    {n : ℕ} (hn : 2 ≤ n) (he : ‖coeff n (fun z => (slitR p : ℂ)*F (q z))‖ = A p n) :
    coeff 2 F = 2 := slit_second_at_equality hp hp1 hq hF (product_of_robertson H1) hn he

theorem composite_slit_deficit (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f)
    {h e : ℂ → ℂ} (hh : IsSchwarz h) (he : IsWeight e) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤
      A p n - slitR p * (coeff n q).re * (1 - ‖e 0 * (deriv h 0)^n‖) :=
  MainReduction.weighted_deficit transfer (proposition_seven H1) hp hp1 hq hf hh he hn

theorem strict_inversion_disk {u : ℂ} (hu : 1 / 2 < u.re) : ‖1/u-1‖ < 1 := by
  have hn : u ≠ 0 := by rintro rfl; norm_num at hu
  rw [show 1/u-1 = (1-u)/u by field_simp, norm_div, div_lt_one (norm_pos_iff.mpr hn)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im]
  nlinarith

theorem convex_binomial_expansion (n : ℕ) (v : ℂ → ℂ) (z : ℂ) :
    (1 + z*v z)^n = ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) * z^j * (v z)^j := by
  rw [add_comm 1 _, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_pow,mul_comm,mul_assoc,mul_left_comm]

theorem equality_forces_unit_derivative (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {n : ℕ} (hn : 1 ≤ n)
    (heq : ‖coeff n (fun z => finitePart (f (h z)))‖ = A p n) : ‖deriv h 0‖ = 1 :=
  MainReduction.derivative_norm_one_of_equality transfer slit_proved (proposition_seven H1) hp hp1 hf hh hn heq

theorem centered_disk_bound (H1 : Robertson) {U : Set Sphere} {w : ℂ} (c : CenteredChart U w)
    {G : ℂ → Sphere} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere))
    {E : ℂ → ℂ} (hE : IsWeight E) {k : ℕ} (hk : 1 ≤ k) :
    ‖coeff k (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ)))‖ ≤ A (poleParam U w) k :=
  centered_disk_of_chart (theorem_one_bound H1) transfer (product_of_robertson H1) c hG hm hw hE hk

end Goodman
