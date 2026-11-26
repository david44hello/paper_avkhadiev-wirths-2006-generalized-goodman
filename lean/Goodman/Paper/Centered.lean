-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Paper.Coefficients
import Goodman.Centered
import Goodman.UniformizationProof

noncomputable section
open Set
namespace Goodman

theorem lemma_eight (H1 : Robertson) (H4 : PlanarRiemannMapping) :
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ),
    IsSource Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U → G x = (w : Sphere) →
    ∀ φ : ℂ → ℂ, Bihol disk Ω φ → φ 0 = x → deriv φ 0 = (radius (planeDomain Ω) x : ℂ) →
    ∀ E : ℂ → ℂ, IsWeight E → ∀ k : ℕ, 1 ≤ k →
      ‖coeff k (fun z => E z * ((finitePart (G (φ z)) - w) / (radius U w : ℂ)))‖ ≤
        A (poleParam U w) k :=
  centeredClaim (theorem_one_bound H1) transfer (product_of_robertson H1)
    (riemannMapping_of_planarRiemannMapping H4)

end Goodman
