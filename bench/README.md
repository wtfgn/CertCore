# bench/ — harness, fuzzer, plot

Empty at M0. M10 builds three things here (all outside the trusted base):

| Component | Milestone | What it does |
|---|---|---|
| Harness | M10.2 | Runs analyzer → checker, records verdict, certificate bytes, analyze/check times into CSV |
| Mutation fuzzer | M10.3 | 10 000 mutated certificates; asserts zero accepts and zero crashes |
| Plot script | M10.4 | The north-star figure: safe-programs vs certificate bytes by label depth, checker time overlaid |

Python is the chosen harness language (plan D9): it writes a certificate mutator
in an hour and — importantly — does not tempt code sharing with the Haskell
analyzer, which would blur the trust boundary.

## Data

Raw CSV is a deliverable and is checked in under `bench/results/`. The plot is
reproducible from the CSV alone; no notebook state, no manual steps.
