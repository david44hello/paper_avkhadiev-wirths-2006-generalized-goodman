-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Alignment
import Goodman.Constants
import Goodman.Extremal
import Goodman.SchwarzCases
import Goodman.SlitTransport
import Goodman.SlitPositivity
import Goodman.SlitWeights
import Goodman.Continuation

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

/-- Rigidity of the transported normalized analytic function at equality. -/
theorem slit_second_at_equality {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {F : ℂ → ℂ} (hF : IsS F)
    (hprod : ProductClaim) {n : ℕ} (hn : 2 ≤ n)
    (he : ‖coeff n (fun z => (slitR p : ℂ) * F (q z))‖ = A p n) :
    coeff 2 F = 2 := by
  let s := Finset.range (n+1)
  let w := fun k : ℕ => (coeff n (fun z => q z ^ k)).re
  have hw (k : ℕ) : 0 ≤ w k := (slit_pow_coeff_nonneg hp hp1 hq k n).2
  have hc (k : ℕ) : coeff n (fun z => q z ^ k) = (w k : ℂ) :=
    Complex.ext rfl (by simpa using (slit_pow_coeff_nonneg hp hp1 hq k n).1)
  have hd (k : ℕ) : ‖coeff k F‖ ≤ (k : ℝ) := by
    cases k with
    | zero => simp [coeff,hF.2.2.1]
    | succ k =>
      simpa only [mul_one] using hprod F hF (fun _ => 1)
        ⟨fun _ _ => analyticAt_const, by simp⟩ _ (Nat.succ_pos k)
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have h1 : coeff 1 F = 1 := by simp [coeff,hF.2.2.2]
  have hR := slitR_pos hp
  have hmass := (slit_weight_sum hp hp1 hq n).trans
    (congrArg Complex.re (coeff_extremal_of_ne_zero hp.ne' n))
  change slitR p * (∑ k ∈ s, (k:ℝ) * w k) = A p n at hmass
  have hqA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  change ‖coeff n (fun z => (slitR p:ℂ) * (F ∘ q) z)‖ = _ at he
  rw [coeff_fun_const_mul, coeff_comp_finite (hF.1 _ h0) hqA hq.2.1,
    norm_mul, Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] at he
  simp_rw [hc] at he
  have hs : ‖∑ i ∈ s, (w i : ℂ) * coeff i F‖ = ∑ i ∈ s, w i * (i:ℝ) := by
    apply mul_left_cancel₀ hR.ne'
    simpa only [mul_comm (w _ : ℂ), mul_comm (w _ : ℝ)] using he.trans hmass.symm
  have hw1 : 0 < w 1 := by simpa [w] using (slit_coeff_pos hp hp1 hq n (by omega)).2
  have hresp := aligned_of_saturated_sum s w (fun k : ℕ => (k : ℝ)) (fun k => coeff k F)
    (fun i _ => hw i) (fun i _ => hd i) (j:=1) (Finset.mem_range.mpr (by omega))
    hw1 h1 (by norm_num) hs 2 (Finset.mem_range.mpr (by omega)) (slit_square_coeff_pos hp hp1 hq hn)
  simpa using hresp

theorem koebe_of_second_eq_two {F : ℂ → ℂ} (hF : IsS F) (h2 : BieberbachSecondRigidity)
    (he : coeff 2 F = 2) : EqOn F (fun z => z / (1 - z)^2) disk := by
  obtain ⟨η,hη,hk⟩ := h2 F hF (by rw [he]; norm_num)
  let K := fun z : ℂ => z / (1-z)^2
  have hn : η ≠ 0 := by intro hz; simp [hz] at hη
  have hsc : (fun z => z / (1 - η*z)^2) = fun z => η⁻¹ * K (η*z) := by
    funext z
    dsimp [K]
    field_simp
  have hf := hk.eventuallyEq_of_mem (Metric.ball_mem_nhds (0:ℂ) zero_lt_one)
  have hh := coeff_congr_of_eventuallyEq hf 2
  rw [he, hsc, coeff_fun_const_mul, coeff_comp_mul_left] at hh
  have hK : coeff 2 K = 2 := by simpa [K] using coeff_koebe 2
  rw [hK] at hh
  have h_eta : η = 1 := by
    field_simp at hh
    exact hh.symm
  simpa [h_eta] using hk

theorem base_rigidity {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    (slit : SlitClaim) (hprod : ProductClaim) (h2 : BieberbachSecondRigidity)
    {n : ℕ} (hn : 2 ≤ n) (he : ‖coeff n (finitePart ∘ f)‖ = A p n) :
    EqOn f (extremal p) disk := by
  obtain ⟨q,hq,_,_⟩ := slit p hp hp1
  obtain ⟨F,hF,hg⟩ := exists_slit_normalized hp hp1 hq hf
  rw [coeff_congr_of_eventuallyEq hg] at he
  have hk := koebe_of_second_eq_two hF h2 (slit_second_at_equality hp hp1 hq hF hprod hn he)
  apply hf.eqOn_of_germ hp hp1 (isM_extremal hp hp1)
  apply hg.trans
  filter_upwards [slitDisk_mem_nhds_zero hp hp1, slit_majorant_germ hp hp1 hq] with z hz h
  rw [hk (hq.1.2.choose_spec.2.1 hz)]
  exact h

theorem higher_equality_of_inputs (transfer : TransferClaim) (slit : SlitClaim)
    (prod : ProductClaim) (deficit : DeficitClaim) (h2 : BieberbachSecondRigidity) : EqualityHigher := by
  intro p hp hp1 f hf h hh n hn
  constructor
  · intro he
    have hr := hh.norm_deriv_eq_one_iff_isRotation.mp
      (MainReduction.derivative_norm_one_of_equality transfer slit deficit hp hp1 hf hh (by omega) he)
    have ha := hr.norm_coeff_comp (finitePart ∘ f) n
    exact ⟨base_rigidity hp hp1 hf slit prod h2 hn (ha.symm.trans he),hr⟩
  · rintro ⟨hff,hr⟩
    change ‖coeff n (fun z => (finitePart ∘ f) (h z))‖ = A p n
    rw [hr.norm_coeff_comp (finitePart ∘ f) n]
    have heq := (hff.comp_left (g:=finitePart)).eventuallyEq_of_mem
      (Metric.ball_mem_nhds (0:ℂ) zero_lt_one)
    rw [coeff_congr_of_eventuallyEq heq,coeff_extremal_of_ne_zero hp.ne',Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (A_positive hp (by omega))]

end Goodman
