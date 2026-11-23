# CertCore

**A verified certificate kernel for abstract interpretation.**
Precision is purchasable with certificate bytes, at a fixed trusted computing base.

| | |
|---|---|
| Status | **M0 — bootstrap.** Build green, trust gates live, certificate format v1 specified. No checker yet: M1–M4 build it |
| Trusted core | Lean 4 (`lean/CertCore/`), no Mathlib |
| Untrusted | Haskell analyzer (M5), Python experiment harness (M10) |
| Interface | JSON certificates, `docs/certificate-v1.md` |
| Licence | MIT |

An untrusted analyzer computes an invariant map and emits a certificate; a small
Lean checker validates it against the operational semantics. If the checker
accepts, the program is safe — as a kernel-checked theorem, not an assertion.

The whole design is one sentence: **move every source of cleverness outside the
trusted base, and make the certificate the only interface.**

## Quick start

The toolchain is pinned by `lean-toolchain` (Lean 4.36.0). With
[elan](https://github.com/leanprover/elan) installed:

```console
$ lake build
Build completed successfully.

$ lake exe certcore
certcore 0.1.0 (M0 bootstrap: checker not implemented yet)

$ lake env lean lean/CertCore/Audit.lean    # axiom audit; silent = clean
```

## Layout

| Path | Role | Trusted? |
|---|---|---|
| `lean/CertCore/I32.lean` | signed 32-bit integers; checked and wrapping arithmetic | **yes** (M1.1) |
| `lean/CertCore/Semantics.lean` | syntax, state and `eval` (M1.2–M1.5), fuel-indexed `step`/`run`, `Safe` (M1.6–M1.7) | **yes** |
| `lean/CertCore/Domain.lean` | `CertDomain` interface, combinators | **yes** (M2, M6) |
| `lean/CertCore/Cert.lean` | certificate type, total JSON decoder | **yes** (M4) |
| `lean/CertCore/Check.lean` | three obligation families, typed diagnostic | **yes** (M3) |
| `lean/CertCore/Proofs.lean` | theorem inventory T1–T10 | **yes** |
| `lean/CertCore/Audit.lean` | `#print axioms check_sound` | **yes** (M3.8) |
| `haskell/` | fixpoint engine, widening, certificate emitter | no (M5) |
| `examples/` | `.imp` benchmark programs | no (M1.11, M10.1) |
| `bench/` | harness, mutation fuzzer, plotting | no (M10) |
| `docs/` | plan, roadmap, theorems, TCB, format | — |

## The trust boundary

Trusted: the Lean kernel and its toolchain, the parser/CFG (written in Lean so
the TCB is one language), the semantics, the certificate decoder, the checker,
and the one generic soundness theorem. Untrusted: everything that proposes
invariants. A buggy widening yields a rejected certificate, never a wrong
verdict. See [`docs/TCB.md`](docs/TCB.md) and the audit command above.

## Documents

- [`docs/introduction.md`](docs/introduction.md) — a from-zero introduction to the ideas and jargon
- [`docs/certcore-project-plan.md`](docs/certcore-project-plan.md) — the *what* and *why*
- [`docs/certcore-roadmap.md`](docs/certcore-roadmap.md) — the *when*; it governs scheduling
- [`docs/THEOREMS.md`](docs/THEOREMS.md) — the theorem contract, T1–T10
- [`docs/certificate-v1.md`](docs/certificate-v1.md) — the wire format
- [`docs/NONGOALS.md`](docs/NONGOALS.md) — the scope fence
- [`docs/known-gaps.md`](docs/known-gaps.md) — anything not proved, documented
- [`docs/prior-art.md`](docs/prior-art.md) — what is borrowed, what is ours

## Reproducing the gates locally

```console
$ lake build                                     # must be silent
$ lake env lean lean/Tests/I32.lean              # executable boundary tests
$ lake env lean lean/Tests/Syntax.lean           # syntax-layer checks
$ lake env lean lean/Tests/State.lean            # state-layer checks
$ lake env lean lean/Tests/Eval.lean             # evaluation checks
$ grep -rnE '\bsorry\b' lean --include='*.lean'  # must print nothing
$ lake env lean lean/CertCore/Audit.lean         # must be silent
```
