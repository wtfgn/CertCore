# TCB — what is trusted, and why

One page. Every trusted component, every trusted translation, and the audit
command. Finalised in M11.5; this is the M1 status with the boundary already
fixed.

## Inside the trusted base

| Component | Where | Why it is trusted |
|---|---|---|
| Lean kernel + its toolchain | external, pinned by `lean-toolchain` (v4.36.0) | The only thing that checks proofs. Lean's kernel is the foundational assumption. |
| Lean's own libraries (`Lean.Data.Json`, `Array`, `Int`) | toolchain, no Mathlib | The decoder needs JSON and integers. No third-party package sits in the TCB (plan D2). |
| `I32` | `I32.lean` (M1.1) | Defines machine arithmetic. Overflow is observable, and the wrap model is proved to agree with the checked one. |
| Parser | planned M4.5 — **not present at M1** | A parser bug changes what "safe" means (plan §10.1, D5). It will be written in Lean so the TCB is one language. |
| Compiler / CFG frontend | `Semantics.lean` (M1.6) | Lowers the AST to the CFG the semantics runs; a bug changes what the program means. `Cmd.compile` takes a size bound and uses a proof-carrying `place`, so no write is silently dropped. `Program.checkWF`/`compileChecked` validate source WF before allocation; `Program.compile_wf` proves successor range. |
| Semantics (`eval`, `step`, `run`, `Safe`, `edges`) | `Semantics.lean` (M1) | *Defines* the safety property. `CFG.step_edge` connects `step` to the checker's edges. |
| Certificate decoder | `Cert.lean` (M4) | Converts untrusted bytes into typed data; must be total. |
| Checker + generic soundness proof | `Check.lean` (M3) | Produces the verdict. |
| The `#print axioms` audit | `Audit.lean` (M1; `check_sound` added at M3.8) | Evidence that the proof rests on nothing extra. |

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
*meaning* of each instruction, but not for array bounds. Source well-formedness
is a decidable check: `Program.checkWF` rejects duplicate or non-dense points,
undeclared arrays, unassigned reads, `maxPoint ≥ maxProgramPoints`, programs with
`maxArrays` or more arrays, any array longer than `maxArrayLength`, and more than
`maxTotalArrayCells` total declared cells; `compileChecked` returns `none`
instead of compiling such a program. `Program.safe` includes `Program.WF`, so a
malformed program is never certified. `Tests/Compile.lean` pins the accepted and
rejected shapes.

Numbers (1) and (2) are the honest residual risk of any Lean artifact; they are
named here rather than hidden. `#print axioms` cannot see them.

## The audit

```console
$ lake env lean lean/CertCore/Audit.lean
```

At M1 the script prints the footprint of `I32.ofIntWrap_agrees`, T1, T2,
`Program.compile_wf`, `Program.compileChecked_wf`, and `CFG.step_edge`. Every
line should be `[propext, Quot.sound]` or strictly smaller. `sorryAx` or
`Classical.choice` appearing is a soundness hole; M11.4 turns the footprint
comparison into a CI gate that fails on any change. M3.8 adds
`#print axioms check_sound`.

Belt and braces: CI also greps `lean/` for a `sorry` token, so an unproved goal
cannot sit in the trusted tree even if the audit script is not run.
