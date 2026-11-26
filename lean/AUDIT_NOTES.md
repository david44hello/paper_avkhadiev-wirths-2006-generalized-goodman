# Assumptions and coefficient conventions

The maps cite the focused v2.70 TeX (MD5 `17b73538f52c9716aa679f0e624af6ed`) and PDF (MD5 `aa74ce744a4e266a883a894785f1ab8d`). The [claim map](CLAIM_MAP.tsv) links mathematical claims to Lean declarations. The [passage inventory](PROOF_STEPS.tsv) also covers definitions, historical attributions and bibliographical material.

The expanded PDF has MD5 `09920c1570f6d864d415a70b2a37ed1f`. Its Lean claim covers the eight numbered results of Sections 1–5. The five Discussion citations locate additional results in the expanded companion, an unrefereed manuscript. The companion is reference [13] in the focused paper and [16] in the expanded paper. The added historical citations in the introduction and Figure 1 supply no new Lean premises. The three open questions are recorded separately in the focused passage inventory.

The comparator checks 214 declarations. The current printed claim rows refer to 210. Four auxiliary results on strict open-disk factors and limiting dilations remain in the reader and comparator: `Goodman.schwarz_of_disk_factor`, `Goodman.strict_of_disk_factor`, `Goodman.dilation_modulus`, and `Goodman.dilation_sharp_limit`.

## Classical results

The following names denote propositions in Lean. A theorem using a proposition takes it as an explicit argument.

| Name | Statement and source |
|---|---|
| Robertson | For an odd normalized univalent function, the sum of the squared moduli of the coefficients of degrees 1, 3, …, 2k−1 is at most k. De Branges proved the remaining Milin inequalities after Grinšpan’s first three cases. The Lebedev–Milin inequality then gives Robertson’s bound. Refereed journal article. [De Branges (1985), pp. 137–138](https://doi.org/10.1007/BF02392821) |
| BieberbachSecondRigidity | Equality in the second coefficient bound for a normalized univalent function forces a rotation of the Koebe function. Bieberbach’s 1916 Berlin Academy proceedings, p. 945, have undocumented refereeing status (treated as UNREFEREED here). The same result appears in a published textbook. [Original proceedings](https://archive.org/download/sitzungsberichte1916deut/sitzungsberichte1916deut.pdf#page=195) · Beliaev (2019), Theorem 3.3, pp. 86–87, DOI `10.1142/9781786346148_0003`. [Crossref chapter record](https://api.crossref.org/works/10.1142/9781786346148_0003) |
| MarxStrohhacker | For a normalized univalent map s of the disk with convex image, the real part of s(z)/z exceeds one half for nonzero z. Refereed journal articles. [Marx (1933), p. 62(d)](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0107/LOG_0006.pdf#page=24) · [Strohhäcker (1933), Satz II, p. 363](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0037/LOG_0039.pdf#page=9) |
| PlanarRiemannMapping | A nonempty, proper, simply connected open subset of the complex plane is biholomorphic to the unit disk. Rudin’s definition in §10.38 uses contraction of loops. The conformal inverse gives the disk-to-domain direction used here. Published textbook, treated as UNREFEREED for this audit. W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, §10.38 and Theorem 14.8, p. 283. |

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
