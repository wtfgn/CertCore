# TCB — what is trusted, and why

One page. Every trusted component, every trusted translation, and the audit
command. Finalised in M11.5; this is the M0 stub with the boundary already
fixed.

## Inside the trusted base

| Component | Where | Why it is trusted |
|---|---|---|
| Lean kernel + its toolchain | external, pinned by `lean-toolchain` (v4.36.0) | The only thing that checks proofs. Lean's kernel is the foundational assumption. |
| Lean's own libraries (`Lean.Data.Json`, `Array`, `Int`) | toolchain, no Mathlib | The decoder needs JSON and integers. No third-party package sits in the TCB (plan D2). |
| Parser + CFG frontend | `lean/CertCore/` (M1) | A parser bug changes what "safe" means (plan §10.1, D5). Written in Lean so the TCB is one language. |
| Semantics (`I32`, `eval`, `step`, `run`, `Safe`) | `Semantics.lean` (M1) | *Defines* the safety property. |
| Certificate decoder | `Cert.lean` (M4) | Converts untrusted bytes into typed data; must be total. |
| Checker + generic soundness proof | `Check.lean` (M3) | Produces the verdict. |
| The `#print axioms` audit | `Audit.lean` (M3.8) | Evidence that the proof rests on nothing extra. |

## Outside the trusted base

- The **Haskell analyzer** (fixpoint engine, widening, label instrumentation,
  certificate emitter, repair loop). Deliberately a different language: the
  boundary is architectural, not a comment.
- The **Python harness** (benchmarks, mutation fuzzer, plotting).
- The **certificates themselves**: every field is untrusted input.

A bug in any of these yields a certificate the checker rejects — not a wrong
verdict. That is requirement R2.

## Trusted translations and assumptions

The audit covers the proof, not the runtime. Explicitly assumed:

1. Lean's kernel implements its logic correctly.
2. The Lean-to-C++-to-binary path preserves semantics (or: proofs are checked
   by a trustworthy build).
3. The operating system and hardware behave.
4. The pinned toolchain is the one that produced the `.olean`/binary being run.

The compiled CFG's **well-formedness** is now proved, not assumed:
`Program.compile_wf` shows the entry and every instruction successor lie inside
the instruction array (`Semantics.lean`). The compiler is still trusted for the
*meaning* of each instruction, but not for array bounds; `Tests/Compile.lean`
pins the bound on representative program shapes.

Numbers (1) and (2) are the honest residual risk of any Lean artifact; they are
named here rather than hidden. `#print axioms` cannot see them.

## The audit

```console
$ lake env lean lean/CertCore/Audit.lean
```

Silent output is clean. Once T5 exists (M3.8), the script contains
`#print axioms check_sound`, and the expected footprint is `[propext, Quot.sound]`
or strictly smaller. `sorryAx` or `Classical.choice` appearing is a soundness
hole; M11.4 turns this into a CI gate that fails on any footprint change.

Belt and braces: CI also greps `lean/` for a `sorry` token, so an unproved goal
cannot sit in the trusted tree even if the audit script is not run.
