-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
open Set
open scoped Topology

namespace Goodman

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

def RiemannMapping : Prop :=
  ∀ U : Set Sphere, IsTarget U → ∀ w : ℂ, (w : Sphere) ∈ U → Nonempty (CenteredChart U w)

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

def IsSegmentOnLineThrough (K : Set Sphere) (w : ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ K = planeDomain (segment ℝ a b) ∧
    ∃ t : ℝ, w = a + (t : ℂ) * (b - a)

/-- Normalized derivative modulus for a map with finite germ at its source point. -/
def derivativeRatio (n : ℕ) (G : ℂ → Sphere) (x : ℂ) (Rs Rt : ℝ) : ℝ :=
  Rs^n * ‖iteratedDeriv n (finitePart ∘ G) x‖ / ((n.factorial : ℝ) * Rt)

def IsSource (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ

def GeometricBound : Prop :=
  ∀ U : Set Sphere, IsTarget U → OnePoint.infty ∈ U →
    ∀ (G : ℂ → Sphere) (w : ℂ), SphereHolomorphicOn G disk → MapsTo G disk U →
    G 0 = (w : Sphere) → (0 < poleParam U w ∧ poleParam U w < 1) ∧
    (∀ n : ℕ, 1 ≤ n → ‖coeff n (finitePart ∘ G)‖ ≤ radius U w * A (poleParam U w) n) ∧
    (∀ n : ℕ, 2 ≤ n →
      (‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n ↔
        BijOn G disk U ∧ IsSegmentOnLineThrough Uᶜ w))

def CenteredClaim : Prop :=
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ),
    IsSource Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U → G x = (w : Sphere) →
    ∀ φ : ℂ → ℂ, Bihol disk Ω φ → φ 0 = x → deriv φ 0 = (radius (planeDomain Ω) x : ℂ) →
    ∀ E : ℂ → ℂ, IsWeight E → ∀ k : ℕ, 1 ≤ k →
      ‖coeff k (fun z => E z * ((finitePart (G (φ z)) - w) / (radius U w : ℂ)))‖ ≤
        A (poleParam U w) k

def DiskDerivativeBound : Prop :=
  ∀ (U : Set Sphere) (x w : ℂ), IsTarget U → x ∈ disk →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G disk → MapsTo G disk U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain disk) x) (radius U w) ≤ D (poleParam U w) ‖x‖ n

def ConvexDerivativeBound : Prop :=
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ), IsSource Ω → Convex ℝ Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain Ω) x) (radius U w) ≤ D (poleParam U w) 1 n

def DiskSharpness : Prop :=
  ∀ (p : ℝ), 0 < p → p ≤ 1 → ∀ x ∈ disk, ∀ n : ℕ, 2 ≤ n →
    ∃ (U : Set Sphere) (G : ℂ → Sphere) (w : ℂ), IsTarget U ∧
    SphereHolomorphicOn G disk ∧ MapsTo G disk U ∧ G x = (w : Sphere) ∧
    poleParam U w = p ∧ derivativeRatio n G x (radius (planeDomain disk) x) (radius U w) =
      D p ‖x‖ n

def ConvexSharpness : Prop :=
  ∀ (p : ℝ), 0 < p → p ≤ 1 → ∀ n : ℕ, 2 ≤ n →
    ∃ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ) (G : ℂ → Sphere),
    IsSource Ω ∧ Convex ℝ Ω ∧ x ∈ Ω ∧ IsTarget U ∧ SphereHolomorphicOn G Ω ∧
    MapsTo G Ω U ∧ G x = (w : Sphere) ∧ poleParam U w = p ∧
    derivativeRatio n G x (radius (planeDomain Ω) x) (radius U w) = D p 1 n

end Goodman
