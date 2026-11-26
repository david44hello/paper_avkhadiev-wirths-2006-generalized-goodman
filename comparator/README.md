# Comparing the Lean statements

The challenge states the coefficient bounds, their equality cases, the derivative estimates and the supporting results used in the paper. Each challenge theorem has an open proof. The solution in the Lean directory supplies the proofs. The comparison permits Lean’s three standard axioms. The four published mathematical results appear as explicit hypotheses on the statements that use them.

To run the comparison on Linux with Git, elan and bubblewrap, start at the root of the checked-out repository.

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp -R comparator/Challenge comparator/Challenge.lean comparator/comparator.json comparator/lakefile.toml "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares the declarations and checks the solution. A successful run ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
