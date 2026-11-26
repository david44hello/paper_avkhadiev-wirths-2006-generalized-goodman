-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Paper.Centered
import Goodman.GeometricTheorem
import Goodman.ConvexDerivative
import Goodman.DiskModels
import Goodman.HalfPlaneModel

noncomputable section
open Set
namespace Goodman

theorem theorem_two_bound (H1 : Robertson) (H4 : PlanarRiemannMapping)
    {U : Set Sphere} (hU : IsTarget U) (hi : OnePoint.infty ∈ U)
    {G : ℂ → Sphere} {w : ℂ} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) :
    (0 < poleParam U w ∧ poleParam U w < 1) ∧
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (finitePart ∘ G)‖ ≤ radius U w * A (poleParam U w) n :=
  geometric_inequality (theorem_one_bound H1) H4 hU hi hG hm hw

theorem theorem_two_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity) (H4 : PlanarRiemannMapping)
    {U : Set Sphere} (hU : IsTarget U) (hi : OnePoint.infty ∈ U)
    {G : ℂ → Sphere} {w : ℂ} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 2 ≤ n) :
    ‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n ↔
      BijOn G disk U ∧ IsSegmentOnLineThrough Uᶜ w :=
  (geometricBound (theorem_one_bound H1) (theorem_one_higher_equality H1 H2) H4 U hU hi G w hG hm hw).2.2 n hn

theorem theorem_three_disk (H1 : Robertson) (H4 : PlanarRiemannMapping) :
  ∀ (U : Set Sphere) (x w : ℂ), IsTarget U → x ∈ disk →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G disk → MapsTo G disk U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain disk) x) (radius U w) ≤ D (poleParam U w) ‖x‖ n :=
  diskDerivativeBound_of_centeredClaim (lemma_eight H1 H4)

theorem theorem_three_convex (H1 : Robertson) (H3 : MarxStrohhacker) (H4 : PlanarRiemannMapping) :
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ), IsSource Ω → Convex ℝ Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain Ω) x) (radius U w) ≤ D (poleParam U w) 1 n :=
  convexDerivativeBound H1 H3 H4

theorem theorem_three_disk_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ x ∈ disk,
  ∃ η : ℂ, ‖η‖ = 1 ∧ (x.im = 0 → 0 ≤ x.re → η = 1) ∧
    let G := fun z => extremal p (η * diskInverse x z)
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G disk ∧ MapsTo G disk (extremalTarget p) ∧
    G x = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G x (radius (planeDomain disk) x)
      (radius (extremalTarget p) 0) = D p ‖x‖ n :=
  diskSharpModel

theorem theorem_three_convex_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    let G := fun z : ℂ => extremal p (z / (1-z))
    IsSource halfPlane ∧ Convex ℝ halfPlane ∧ (0 : ℂ) ∈ halfPlane ∧
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G halfPlane ∧ MapsTo G halfPlane (extremalTarget p) ∧
    G 0 = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G 0 (radius (planeDomain halfPlane) 0)
      (radius (extremalTarget p) 0) = D p 1 n :=
  convexSharpModel

end Goodman
