# The Goodman coefficient problem

The paper bounds the Taylor coefficients at zero of a weighted composition. A meromorphic function can have a pole elsewhere in the disk. Its coefficients here are its iterated derivatives at zero divided by the corresponding factorials. The target class uses the Riemann sphere. A simple pole is a simple zero in the reciprocal coordinate, and injectivity includes that point at infinity.

## Results and assumptions

| Result | Where to read it | Explicit hypotheses |
|---|---|---|
| Theorem 1, weighted bound | [Coefficient theorems](Goodman/Paper/Coefficients.lean) | Robertson |
| Theorem 1, equality for weight one | [Rigidity proof](Goodman/Rigidity.lean) · [First coefficient](Goodman/SchwarzCases.lean) | Robertson and BieberbachSecondRigidity for degrees at least two. The first coefficient uses the standard axioms alone. |
| Theorem 2, geometric estimate | [Geometric theorems](Goodman/Paper/Geometry.lean) · [Segment construction](Goodman/SegmentGeometry.lean) | Robertson and PlanarRiemannMapping for the bound. The equality characterization also uses BieberbachSecondRigidity. |
| Theorem 3, derivative estimates | [Disk source](Goodman/DiskDerivative.lean) · [Convex source](Goodman/ConvexDerivative.lean) | Robertson and PlanarRiemannMapping for the disk. The convex-source bound also uses MarxStrohhacker. |
| Theorem 3, sharpness | [Disk extremal](Goodman/DiskModels.lean) · [Half-plane extremal](Goodman/HalfPlaneModel.lean) | Standard axioms alone. Each model attains equality at every order simultaneously. |
| Lemma 4, weighted transfer | [Transfer](Goodman/Transfer.lean) | Standard axioms alone. |
| Lemma 5, slit map | [Slit map](Goodman/Slit.lean) | Standard axioms alone. |
| Lemma 6, product estimate | [Product estimate](Goodman/Product.lean) | Robertson |
| Proposition 7, deficit | [Coefficient theorems](Goodman/Paper/Coefficients.lean) | Robertson |
| Lemma 8, centered coefficient | [Centered theorem](Goodman/Paper/Centered.lean) | Robertson and PlanarRiemannMapping |

The formal proof of the general weighted transfer constructs bounded multipliers using the Poisson kernel and passes to a locally uniform limit. This yields one multiplier for every analytic test germ and includes degree zero. The paper also gives a proof by duality. For weight one its explicit reversed polynomial is verified using Carathéodory’s coefficient inequality, which has a Lean proof. [Weighted construction](Goodman/Transfer.lean) · [Reversed polynomial](Goodman/UnweightedTransfer.lean) · [Positive-real-part bound](Goodman/Caratheodory.lean)

## Classical results

The following names denote propositions in Lean. A theorem using a proposition takes it as an explicit argument.

| Name | Statement and source |
|---|---|
| Robertson | For an odd normalized univalent function, the sum of the squared moduli of the coefficients of degrees 1, 3, …, 2k−1 is at most k. De Branges proved the remaining Milin inequalities after Grinšpan’s first three cases. The Lebedev–Milin inequality then gives Robertson’s bound. Refereed journal article. [De Branges (1985), pp. 137–138](https://doi.org/10.1007/BF02392821) |
| BieberbachSecondRigidity | Equality in the second coefficient bound for a normalized univalent function forces a rotation of the Koebe function. Bieberbach’s 1916 Berlin Academy proceedings, p. 945, have undocumented refereeing status (treated as UNREFEREED here). The same result appears in a published textbook. [Original proceedings](https://archive.org/download/sitzungsberichte1916deut/sitzungsberichte1916deut.pdf#page=195) · Beliaev (2019), Theorem 3.3, pp. 86–87, DOI `10.1142/9781786346148_0003`. [Crossref chapter record](https://api.crossref.org/works/10.1142/9781786346148_0003) |
| MarxStrohhacker | For a normalized univalent map s of the disk with convex image, the real part of s(z)/z exceeds one half for nonzero z. Refereed journal articles. [Marx (1933), p. 62(d)](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0107/LOG_0006.pdf#page=24) · [Strohhäcker (1933), Satz II, p. 363](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0037/LOG_0039.pdf#page=9) |
| PlanarRiemannMapping | A nonempty, proper, simply connected open subset of the complex plane is biholomorphic to the unit disk. Rudin’s definition in §10.38 uses contraction of loops. The conformal inverse gives the disk-to-domain direction used here. Published textbook, treated as UNREFEREED for this audit. W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, §10.38 and Theorem 14.8, p. 283. |

## Checking the proof library

The [reader command](README.md#how-to-verify) builds the solution and reports each theorem’s axioms and named mathematical hypotheses. The [comparator](../comparator/README.md) checks the solution against independent statements of the 214 theorems. Its paranoid mode also runs Lean’s paranoid kernel, lean4lean, nanoda, con-leche and con-ron. The release checks include a fresh reader build, a kernel replay of the compiled solution modules and a separate check of a single declaration export with all six kernels.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
