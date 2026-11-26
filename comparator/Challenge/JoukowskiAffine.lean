-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
namespace Goodman

def restoreValue (w a : ℂ) : Sphere → Sphere := OnePoint.map (fun v => w + a * v)

def slitJoukowskiAffine (p : ℝ) : Sphere → Sphere :=
  restoreValue (2 * (slitR p : ℂ) - 2) (slitR p)

end Goodman
