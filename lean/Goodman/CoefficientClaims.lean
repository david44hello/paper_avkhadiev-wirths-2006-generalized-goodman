-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

def WeightedBound : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e →
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤ A p n

def EqualityHigher : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ n : ℕ, 2 ≤ n →
    (‖coeff n (fun z => finitePart (f (h z)))‖ = A p n ↔
      EqOn f (extremal p) disk ∧ IsRotation h)

def EqualityFirst : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h →
    (‖coeff 1 (fun z => finitePart (f (h z)))‖ = A p 1 ↔ IsRotation h)

def TransferClaim : Prop :=
  ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e → ∀ n : ℕ,
    ∃ E : ℂ → ℂ, IsWeight E ∧ E 0 = e 0 * (deriv h 0)^n ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
        coeff n (fun z => e z * g (h z)) = coeff n (fun w => E w * g w)

def SlitClaim : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 → ∃ q : ℂ → ℂ, IsSlitMap p q ∧
    (∀ n : ℕ, 1 ≤ n → (coeff n q).im = 0 ∧ 0 < (coeff n q).re) ∧
    (∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (finitePart (extremal p z)))

def ProductClaim : Prop :=
  ∀ F : ℂ → ℂ, IsS F → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ k : ℕ, 1 ≤ k → ‖coeff k (fun z => F z * E z)‖ ≤ (k : ℝ)

def DeficitClaim : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ q : ℂ → ℂ, IsSlitMap p q →
    ∀ f : ℂ → Sphere, IsM p f → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ n : ℕ, 1 ≤ n →
      ‖coeff n (fun z => E z * finitePart (f z))‖ ≤
        A p n - slitR p * (coeff n q).re * (1 - ‖E 0‖)

end Goodman
