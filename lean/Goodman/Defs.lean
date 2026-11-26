-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

abbrev Sphere := OnePoint ℂ

def disk : Set ℂ := Metric.ball 0 1

def coeff (n : ℕ) (g : ℂ → ℂ) : ℂ := iteratedDeriv n g 0 / n.factorial

def IsWeight (e : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ e disk ∧ ∀ z ∈ disk, ‖e z‖ ≤ 1

def IsSchwarz (h : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ h disk ∧ MapsTo h disk disk ∧ h 0 = 0

def IsS (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F disk ∧ InjOn F disk ∧ F 0 = 0 ∧ deriv F 0 = 1

/-- The affine coordinate, with a filler at infinity. Coefficients use it only at finite germs. -/
def finitePart (w : Sphere) : ℂ := (show Option ℂ from w).getD 0

/-- The inverse chart maps its coordinate zero to the point at infinity. -/
def fromRecip (z : ℂ) : Sphere := if z = 0 then OnePoint.infty else (z⁻¹ : ℂ)

def SphereHolomorphicOn (F : ℂ → Sphere) (U : Set ℂ) : Prop :=
  ∀ x ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧
    ((∀ᶠ z in 𝓝 x, F z = (g z : Sphere)) ∨
      (∀ᶠ z in 𝓝 x, F z = fromRecip (g z)))

def SimplePoleAt (F : ℂ → Sphere) (p : ℂ) : Prop :=
  ∃ u : ℂ → ℂ, AnalyticAt ℂ u p ∧ u p = 0 ∧ deriv u p ≠ 0 ∧
    ∀ᶠ z in 𝓝 p, F z = fromRecip (u z)

def IsM (p : ℝ) (F : ℂ → Sphere) : Prop :=
  SphereHolomorphicOn F disk ∧ InjOn F disk ∧ F (p : ℂ) = OnePoint.infty ∧
  SimplePoleAt F p ∧ F 0 = (0 : ℂ) ∧ deriv (finitePart ∘ F) 0 = 1

def IsRotation (h : ℂ → ℂ) : Prop :=
  ∃ a : ℂ, ‖a‖ = 1 ∧ EqOn h (fun z => a * z) disk

/-- Coefficient of the extremal function, including the planar endpoint p = 1. -/
def A (p : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, p ^ (2 * j)) / p ^ (n - 1)

def D (p r : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((n - 1).choose j : ℝ) * r ^ (n - 1 - j) * A p (j + 1)

def extremal (p : ℝ) (z : ℂ) : Sphere :=
  let den := (1 - (p : ℂ) * z) * (1 - z / (p : ℂ))
  if den = 0 then OnePoint.infty else (z / den : ℂ)

def slitR (p : ℝ) : ℝ := 4 * p / (1 + p) ^ 2

def slitDisk (p : ℝ) : Set ℂ :=
  disk \ ((fun x : ℝ => (x : ℂ)) '' Ico p 1)

def Bihol (U V : Set ℂ) (q : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ q U ∧ ∃ χ : ℂ → ℂ, AnalyticOnNhd ℂ χ V ∧
    MapsTo q U V ∧ MapsTo χ V U ∧ LeftInvOn χ q U ∧ LeftInvOn q χ V

/-- The origin-normalized biholomorphism and its cleared Joukowski identity. -/
def IsSlitMap (p : ℝ) (q : ℂ → ℂ) : Prop :=
  Bihol (slitDisk p) disk q ∧ q 0 = 0 ∧
    ∀ z ∈ slitDisk p, z * (1 + q z)^2 = (slitR p : ℂ) * q z * (1 + z)^2

/-- Robertson's bound for odd normalized univalent functions. De Branges, Acta Math. 154
(1985), pp. 137–138 (refereed), proves the remaining cases of Milin's conjecture after
Grinšpan's first three. The Lebedev–Milin inequality implies Robertson's inequality. -/
def Robertson : Prop :=
  ∀ φ : ℂ → ℂ, IsS φ → (∀ z ∈ disk, φ (-z) = -φ z) →
    ∀ k : ℕ, 1 ≤ k → (∑ j ∈ Finset.range k, ‖coeff (2*j+1) φ‖^2) ≤ (k : ℝ)

/-- The equality case at the second coefficient: Bieberbach, Berlin Academy proceedings
(1916), p. 945 (individual refereeing undocumented, treated as UNREFEREED). Also stated in
Beliaev, Conformal Maps and Geometry (2019), Theorem 3.3, pp. 86–87, a published textbook. -/
def BieberbachSecondRigidity : Prop :=
  ∀ F : ℂ → ℂ, IsS F → ‖coeff 2 F‖ = 2 →
    ∃ η : ℂ, ‖η‖ = 1 ∧ EqOn F (fun z => z / (1 - η*z)^2) disk

/-- Marx, Math. Ann. 107 (1933), p. 62(d), and Strohhäcker, Math. Z. 37 (1933),
Satz II, p. 363 (refereed), for convex normalized univalent functions. -/
def MarxStrohhacker : Prop :=
  ∀ s : ℂ → ℂ, IsS s → Convex ℝ (s '' disk) →
    ∀ z ∈ disk, z ≠ 0 → 1 / 2 < (s z / z).re

end Goodman
