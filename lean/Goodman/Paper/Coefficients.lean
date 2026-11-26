-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Transfer
import Goodman.Product
import Goodman.Deficit
import Goodman.Slit
import Goodman.Rigidity

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem theorem_one_bound (H1 : Robertson) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e →
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤ A p n :=
  MainReduction.weighted_of_transfer_slit_deficit transfer slit_proved (deficit_of_product (product_of_robertson H1))

theorem theorem_one_higher_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ n : ℕ, 2 ≤ n →
    (‖coeff n (fun z => finitePart (f (h z)))‖ = A p n ↔
      EqOn f (extremal p) disk ∧ IsRotation h) :=
  higher_equality_of_inputs transfer slit_proved (product_of_robertson H1) (deficit_of_product (product_of_robertson H1)) H2

theorem theorem_one_first_equality :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h →
    (‖coeff 1 (fun z => finitePart (f (h z)))‖ = A p 1 ↔ IsRotation h) :=
  equalityFirst

theorem lemma_four :
  ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e → ∀ n : ℕ,
    ∃ E : ℂ → ℂ, IsWeight E ∧ E 0 = e 0 * (deriv h 0)^n ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
        coeff n (fun z => e z * g (h z)) = coeff n (fun w => E w * g w) :=
  transfer

theorem lemma_five :
  ∀ (p : ℝ), 0 < p → p < 1 → ∃ q : ℂ → ℂ, IsSlitMap p q ∧
    (∀ n : ℕ, 1 ≤ n → (coeff n q).im = 0 ∧ 0 < (coeff n q).re) ∧
    (∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (finitePart (extremal p z))) :=
  slit_proved

theorem lemma_six (H1 : Robertson) :
  ∀ F : ℂ → ℂ, IsS F → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ k : ℕ, 1 ≤ k → ‖coeff k (fun z => F z * E z)‖ ≤ (k : ℝ) :=
  product_of_robertson H1

theorem proposition_seven (H1 : Robertson) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ q : ℂ → ℂ, IsSlitMap p q →
    ∀ f : ℂ → Sphere, IsM p f → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ n : ℕ, 1 ≤ n →
      ‖coeff n (fun z => E z * finitePart (f z))‖ ≤
        A p n - slitR p * (coeff n q).re * (1 - ‖E 0‖) :=
  deficit_of_product (product_of_robertson H1)

theorem base_coefficient_bound (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (finitePart ∘ f)‖ ≤ A p n := by
  have hid : IsSchwarz id := ⟨fun _ _ => analyticAt_id, mapsTo_id _, rfl⟩
  simpa [Function.comp_def] using theorem_one_bound H1 p hp hp1 f hf id hid (fun _ => 1)
    ⟨fun _ _ => analyticAt_const, by simp⟩ n hn

end Goodman
