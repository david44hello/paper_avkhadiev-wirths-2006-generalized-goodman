-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Defs

noncomputable section
namespace Goodman

def slitArcRe (p x : ℝ) : ℝ := (slitR p * (x + x⁻¹ + 2) - 2) / 2

end Goodman
