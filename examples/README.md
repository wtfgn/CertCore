# examples/ — `.imp` programs

The surface syntax is specified in
[`docs/imp-syntax.md`](../docs/imp-syntax.md). The first three fixtures (M1.11)
are:

| File | Expected |
|---|---|
| [`safe.imp`](safe.imp) | runs to halt with `x = 3`, `y = 1` |
| [`div-zero.imp`](div-zero.imp) | fails at `10 / x` with `x = 0` |
| [`array-overflow.imp`](array-overflow.imp) | fails storing `a[3]` in an array of length 3 |

M10.1 grows the suite to ~30 programs in five families (plan §13.1):

| Family | n | Purpose |
|---|---|---|
| Straight-line arithmetic | 6 | Baseline; overflow cases |
| Loops needing widening | 6 | Where intervals lose precision |
| Array bounds | 6 | The classic safety property |
| Path-sensitive (intervals provably fail; labels win) | 8 | The C3/C4 experiment |
| Small realistic kernels (binary search, bubble sort, string copy, gcd) | 4 | Plausibility |

## Naming

`family-number-name.imp`, e.g. `array-bounds-03-find.imp`. Each file carries a
header comment with the expected verdict and the configuration expected to prove
it:

```
// expect: safe      config: interval, depth 0
// expect: unsafe    config: none (division by zero at point 4)
```

The suite is published *including* the programs no configuration certifies —
those are the interesting rows of the frontier plot (plan §13.4).
