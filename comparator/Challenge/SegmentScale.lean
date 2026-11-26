-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
namespace Goodman

def segmentScale (near far : ℝ) : ℝ := 4 * near * far / (far - near)

end Goodman
