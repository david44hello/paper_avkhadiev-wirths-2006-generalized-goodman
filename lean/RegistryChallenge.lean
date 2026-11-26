-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Mathlib

@[expose] public section

/-! # The generalized Goodman coefficient and derivative bounds
The four literature inputs are explicit propositions. -/

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

def Bihol (U V : Set ℂ) (q : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ q U ∧ ∃ χ : ℂ → ℂ, AnalyticOnNhd ℂ χ V ∧
    MapsTo q U V ∧ MapsTo χ V U ∧ LeftInvOn χ q U ∧ LeftInvOn q χ V

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

def IsTarget (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsSimplyConnected U ∧ ∃ a b : Sphere, a ∉ U ∧ b ∉ U ∧ a ≠ b

/-- Holomorphy of a plane-valued map on a spherical open set, in the two standard charts. -/
def HolomorphicFromSphereOn (g : Sphere → ℂ) (U : Set Sphere) : Prop :=
  (∀ z : ℂ, (z : Sphere) ∈ U → AnalyticAt ℂ (fun t : ℂ => g (t : Sphere)) z) ∧
  (OnePoint.infty ∈ U → AnalyticAt ℂ (g ∘ fromRecip) 0)

/-- Disk parametrization with mutually inverse holomorphic maps and a specified finite center. -/
structure CenteredChart (U : Set Sphere) (w : ℂ) where
  forward : ℂ → Sphere
  inverse : Sphere → ℂ
  forward_holo : SphereHolomorphicOn forward disk
  inverse_holo : HolomorphicFromSphereOn inverse U
  forward_maps : MapsTo forward disk U
  inverse_maps : MapsTo inverse U disk
  left_inverse : LeftInvOn inverse forward disk
  right_inverse : LeftInvOn forward inverse U
  center : forward 0 = (w : Sphere)

def planeDomain (Ω : Set ℂ) : Set Sphere := (fun z : ℂ => (z : Sphere)) '' Ω

def radius (U : Set Sphere) (w : ℂ) : ℝ := by
  classical
  exact if h : Nonempty (CenteredChart U w) then
    ‖deriv (finitePart ∘ h.some.forward) 0‖ else 0

/-- Pull back the curvature-minus-four disk distance from the chart center.
For finite center w, the disk formula is artanh of the norm of the other point's preimage. -/
def hypDistanceFrom (U : Set Sphere) (w : ℂ) (v : Sphere) : ℝ := by
  classical
  exact if h : Nonempty (CenteredChart U w) then
    Real.artanh ‖h.some.inverse v‖ else 0

def poleParam (U : Set Sphere) (w : ℂ) : ℝ := by
  classical
  exact if OnePoint.infty ∈ U then Real.tanh (hypDistanceFrom U w OnePoint.infty) else 1

/-- Normalized derivative modulus for a map with finite germ at its source point. -/
def derivativeRatio (n : ℕ) (G : ℂ → Sphere) (x : ℂ) (Rs Rt : ℝ) : ℝ :=
  Rs^n * ‖iteratedDeriv n (finitePart ∘ G) x‖ / ((n.factorial : ℝ) * Rt)

def IsSource (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ

/-- The planar Riemann mapping theorem. Rudin, Real and Complex Analysis, third edition,
§10.38 and Theorem 14.8 (p. 283), uses the loop definition of simple connectivity. Taking
the conformal inverse gives the disk-to-domain formulation. Published textbook, classified
UNREFEREED for the source audit. -/
def PlanarRiemannMapping : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsSimplyConnected U → U ≠ Set.univ →
    ∃ φ : ℂ → ℂ, Bihol disk U φ

def diskInverse (x z : ℂ) : ℂ := (z - x) / (1 - star x * z)

/-- The numeral two satisfies the lower bound used by the real numeral instance. -/
theorem halfPlane._proof_1 : (1 + 1 : ℕ).AtLeastTwo :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

attribute [local instance 2000] halfPlane._proof_1 in
def halfPlane : Set ℂ := {z | z.re < 1 / 2}

def extremalTarget (p : ℝ) : Set Sphere := extremal p '' disk

/-- The generalized Goodman coefficient conjecture, with Robertson’s inequality as input. -/
theorem unweighted_goodman (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => finitePart (f (h z)))‖ ≤ A p n := by sorry

/-- The coefficient bound with a bounded holomorphic weight, assuming Robertson’s inequality. -/
theorem theorem_one_bound (H1 : Robertson) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e →
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤ A p n := by sorry

/-- Unweighted equality at degree at least two, assuming Robertson and Bieberbach’s rigidity theorem. -/
theorem theorem_one_higher_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ n : ℕ, 2 ≤ n →
    (‖coeff n (fun z => finitePart (f (h z)))‖ = A p n ↔
      EqOn f (extremal p) disk ∧ IsRotation h) := by sorry

/-- Unweighted equality at degree one holds exactly for rotations of the inner map. -/
theorem theorem_one_first_equality :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h →
    (‖coeff 1 (fun z => finitePart (f (h z)))‖ = A p 1 ↔ IsRotation h) := by sorry

/-- The disk derivative bound from Robertson’s inequality and the planar Riemann mapping theorem. -/
theorem theorem_three_disk (H1 : Robertson) (H4 : PlanarRiemannMapping) :
  ∀ (U : Set Sphere) (x w : ℂ), IsTarget U → x ∈ disk →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G disk → MapsTo G disk U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain disk) x) (radius U w) ≤ D (poleParam U w) ‖x‖ n := by sorry

/-- The convex-source bound from Robertson, Marx–Strohhäcker and planar Riemann mapping. -/
theorem theorem_three_convex (H1 : Robertson) (H3 : MarxStrohhacker) (H4 : PlanarRiemannMapping) :
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ), IsSource Ω → Convex ℝ Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain Ω) x) (radius U w) ≤ D (poleParam U w) 1 n := by sorry

/-- For each pole parameter and center, one disk map attains equality at every order at least two. -/
theorem theorem_three_disk_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ x ∈ disk,
  ∃ η : ℂ, ‖η‖ = 1 ∧ (x.im = 0 → 0 ≤ x.re → η = 1) ∧
    let G := fun z => extremal p (η * diskInverse x z)
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G disk ∧ MapsTo G disk (extremalTarget p) ∧
    G x = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G x (radius (planeDomain disk) x)
      (radius (extremalTarget p) 0) = D p ‖x‖ n := by sorry

/-- For each pole parameter, one half-plane map attains equality at every order at least two. -/
theorem theorem_three_convex_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    let G := fun z : ℂ => extremal p (z / (1-z))
    IsSource halfPlane ∧ Convex ℝ halfPlane ∧ (0 : ℂ) ∈ halfPlane ∧
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G halfPlane ∧ MapsTo G halfPlane (extremalTarget p) ∧
    G 0 = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G 0 (radius (planeDomain halfPlane) 0)
      (radius (extremalTarget p) 0) = D p 1 n := by sorry

end Goodman
