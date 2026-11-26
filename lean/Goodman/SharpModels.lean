-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Geometry

@[expose] public section

noncomputable section
open Set Complex
namespace Goodman

def diskInverse (x z : ℂ) : ℂ := (z - x) / (1 - star x * z)

def halfPlane : Set ℂ := {z | z.re < 1 / 2}

def extremalTarget (p : ℝ) : Set Sphere := extremal p '' disk

/-- The real-center model in the disk and its rotations. One map works for every order. -/
def DiskSharpModel : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ x ∈ disk,
  ∃ η : ℂ, ‖η‖ = 1 ∧ (x.im = 0 → 0 ≤ x.re → η = 1) ∧
    let G := fun z => extremal p (η * diskInverse x z)
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G disk ∧ MapsTo G disk (extremalTarget p) ∧
    G x = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G x (radius (planeDomain disk) x)
      (radius (extremalTarget p) 0) = D p ‖x‖ n

/-- The fixed left half-plane model attains every order at the origin. -/
def ConvexSharpModel : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    let G := fun z : ℂ => extremal p (z / (1-z))
    IsSource halfPlane ∧ Convex ℝ halfPlane ∧ (0 : ℂ) ∈ halfPlane ∧
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G halfPlane ∧ MapsTo G halfPlane (extremalTarget p) ∧
    G 0 = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G 0 (radius (planeDomain halfPlane) 0)
      (radius (extremalTarget p) 0) = D p 1 n

end Goodman
