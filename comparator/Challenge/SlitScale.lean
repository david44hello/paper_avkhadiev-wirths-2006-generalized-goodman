-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
namespace Goodman

def slitC (p : ℝ) : ℝ := (1 - p)^2 / (4 * p)

end Goodman
