# The generalized Goodman conjecture

The paper’s link is on the [front page of this repository](https://github.com/david44hello/paper_avkhadiev-wirths-2006-generalized-goodman).

The weighted coefficient bound uses Robertson’s inequality for odd univalent functions. De Branges proved the remaining cases of Milin’s conjecture after Grinšpan’s first three. The Lebedev–Milin inequality gives Robertson’s bound. Equality in degrees two and higher also uses Bieberbach’s equality case for the second coefficient of a normalized univalent function. [De Branges (1985), pp. 137–138](https://doi.org/10.1007/BF02392821) · [Bieberbach (1916), p. 945](https://archive.org/download/sitzungsberichte1916deut/sitzungsberichte1916deut.pdf#page=195) · Beliaev (2019), Theorem 3.3, pp. 86–87, DOI `10.1142/9781786346148_0003`. [Crossref chapter record](https://api.crossref.org/works/10.1142/9781786346148_0003)

The geometric estimates use the **planar** Riemann mapping theorem (Rudin, Theorem 14.8). The convex-source upper bound additionally uses the Marx–Strohhäcker inequality Re(s(z)/z) > 1/2 for a normalized convex map at nonzero z. The transfer lemma, slit map and explicit sharpness examples use only Lean’s standard axioms. W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, §10.38 and Theorem 14.8, p. 283. [Marx, p. 62(d)](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0107/LOG_0006.pdf#page=24) · [Strohhäcker, Satz II](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0037/LOG_0039.pdf#page=9)

The [reading guide](WHAT_TO_READ.md) gives the exact assumptions and points to each proof.

## How to verify

Install Git, Python 3 and elan. Run the following command from the `lean/` directory.

```sh
./scripts/check.sh
```

The command verifies the two generated audit files and reports the axioms and named hypotheses for each listed theorem. Its last line is

```text
Checked 214 Lean declarations against the three permitted standard axioms.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
