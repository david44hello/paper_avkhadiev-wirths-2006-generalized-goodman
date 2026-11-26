-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Defs

namespace Goodman

/-- The planar Riemann mapping theorem. Rudin, Real and Complex Analysis, third edition,
§10.38 and Theorem 14.8 (p. 283), uses the loop definition of simple connectivity. Taking
the conformal inverse gives the disk-to-domain formulation. Published textbook, classified
UNREFEREED for the source audit. -/
def PlanarRiemannMapping : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsSimplyConnected U → U ≠ Set.univ →
    ∃ φ : ℂ → ℂ, Bihol disk U φ

end Goodman
