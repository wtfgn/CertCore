# NONGOALS — the scope fence

Deliberate exclusions, not deferred-by-accident work. Revisiting one of these
requires a plan amendment, not a pull request.

## Language and semantics

| Excluded | Why |
|---|---|
| C, machine code, or any real ISA | The kernel is the deliverable; the language is a fixture. The semantics would dominate the month (plan §8.2). Plug point sketched in plan §16. |
| Floating point | Verasco needed a thesis for this; it is not the kernel's problem. |
| Procedures, recursion | Requires summaries and a compositional certificate theory — a second project. |
| Heap, pointers, aliasing | Requires a separation-logic certificate layer. |
| Concurrency | Requires rely-guarantee certificates; the hardest open area. |
| Real integer division semantics beyond `Imp`'s | The language is a fixture; only the safety property matters. |

## Analysis and certificate theory

| Excluded | Why |
|---|---|
| Disjunctive (matching-based) domain | Inclusion becomes a search, violating R4. Path sensitivity is obtained as a product instead (plan §4.4, §7.5). This is the open problem we leave. |
| Completeness of inclusion for octagons | Documented limitation, not a bug. |
| Invariant *inference* quality | The analyzer is a driver, not a contribution. If it is good, that is a bonus. |
| Reduced product in the 4-week artifact | Post-month (M8); see roadmap §4.1. The in-month claim C2 is product-only. |
| Octagons in the 4-week artifact | Post-month (M7). The domain axis of the north-star plot is deferred; label depth carries the axis instead. |

## Evaluation

| Excluded | Why |
|---|---|
| Head-to-head benchmark vs Verasco / Astrée | Infeasible across 2015 toolchains and a different language; plan §13.4 explains what is measured instead, and why that is honest. |
| A claim of scalability on real code | Thirty programs establish *shape*, not scale. Stated in threats to validity. |
| Certificates of *unsafety* | Out of scope; noted as a limitation in the write-up. |
| Completeness of the safety verdict | The checker rejects some valid invariants. Documented, not fixed. |

## What "no" means here

A non-goal is a fence, not a TODO. The two failure modes it prevents are scope
drift (toward real C) and stall (proving one hard lemma for three weeks). If a
proposed change crosses a line in this file, the conversation is about the plan,
not about the patch.
