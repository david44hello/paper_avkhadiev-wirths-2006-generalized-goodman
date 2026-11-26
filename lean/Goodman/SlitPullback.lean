-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Paper.Coefficients

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

/-- The bound on the multiplier in slit coordinates and the exact function and coefficient
identities hold on the full domains of the inverse charts. -/
theorem weighted_slit_pullback (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f)
    {E : ℂ → ℂ} (hE : IsWeight E) :
    ∃ χ F : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ IsS F ∧ IsWeight (E ∘ χ) ∧
    EqOn F (fun w => finitePart (f (χ w)) / (slitR p : ℂ)) disk ∧
    (∀ z ∈ slitDisk p, E z * finitePart (f z) = (slitR p : ℂ) * (F (q z) * E (χ (q z)))) ∧
    coeff 1 (fun w => F w * E (χ w)) = E 0 ∧
    ∀ k : ℕ, 1 ≤ k → ‖coeff k (fun w => F w * E (χ w))‖ ≤ (k : ℝ) := by
  obtain ⟨χ,F,hχ,hm,hl,_,hχ0,_,hF,hForm,he⟩ := full_slit_coordinates hp hp1 hq hf
  have hW : IsWeight (E ∘ χ) :=
    ⟨hE.1.comp hχ.1 (fun w hw => (hm hw).1), fun w hw => hE.2 _ (hm hw).1⟩
  have h0 : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one
  refine ⟨χ,F,hχ,hF,hW,hForm,?_,?_,lemma_six H1 F hF _ hW⟩
  · intro z hz
    rw [hl hz,he z hz]
    ring
  · simpa [coeff,hF.2.2.2,hF.2.2.1,hχ0] using
      ((hF.1 0 h0).differentiableAt.hasDerivAt.fun_mul (hW.1 0 h0).differentiableAt.hasDerivAt).deriv

/-- At equality, the normalized map in slit coordinates is the Koebe function on the disk.
The identities giving the original meromorphic map then hold on the entire slit disk. -/
theorem full_slit_restoration (H1 : Robertson) (H2 : BieberbachSecondRigidity)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ} (hq : IsSlitMap p q)
    {f : ℂ → Sphere} (hf : IsM p f) {n : ℕ} (hn : 2 ≤ n)
    (heq : ‖coeff n (finitePart ∘ f)‖ = A p n) :
    ∃ F : ℂ → ℂ, IsS F ∧ EqOn F (fun z => z/(1-z)^2) disk ∧
      ∀ z ∈ slitDisk p, finitePart (f z) = (slitR p : ℂ)*F (q z) ∧
        (slitR p : ℂ)*F (q z) = finitePart (extremal p z) := by
  obtain ⟨_,F,_,_,_,_,_,_,hF,_,he⟩ := full_slit_coordinates hp hp1 hq hf
  have near : finitePart ∘ f =ᶠ[𝓝 (0:ℂ)] fun z => (slitR p : ℂ)*F (q z) := by
    filter_upwards [slitDisk_mem_nhds_zero hp hp1] with z hz using he z hz
  have hcoeff := (coeff_congr_of_eventuallyEq near n)
  have hk := koebe_of_second_eq_two hF H2 (slit_second_at_equality hp hp1 hq hF
    (product_of_robertson H1) hn ((congrArg norm hcoeff).symm.trans heq))
  have hext := base_rigidity hp hp1 hf slit_proved (product_of_robertson H1) H2 hn heq
  exact ⟨F,hF,hk,fun z hz => ⟨he z hz,(he z hz).symm.trans (congrArg finitePart (hext hz.1))⟩⟩

end Goodman
