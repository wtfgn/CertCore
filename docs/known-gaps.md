# known-gaps

Anything in the trusted tree that is not proved, or is proved only under a
stated limitation, is recorded here. `main` never carries an undocumented gap
(roadmap §2, rule 5).

Format: one row per gap, with the lemma/theorem it blocks, the milestone that
owns it, and whether it is a *deferral* (planned) or a *limitation* (won't fix).

| # | Gap | Blocks | Owner | Kind | Resolution |
|---|---|---|---|---|---|
| — | *(no `sorry`; the F1 interface fields are proved for intervals; the audit is clean after F2)* | — | — | — | Every listed trusted lemma depends on `[propext, Quot.sound]` or smaller; CI fails on `Classical.choice`/`sorryAx`. T8's generic completeness field is a pending M4 contract decision (see the limitation below). |

## Standing limitations (not gaps)

These are true by design and will be documented in the write-up rather than
fixed:

- **Arithmetic transfer collapses to `top` on endpoint overflow**, and
  multiplication and division are `top` at M2.8. This is a precision limitation,
  not a soundness one: T4c is proved for the conservative transfer, and the
  checker's safety obligations separately rule out overflow on accepted
  executions. Array read/len became precise at M2.7. Store transfer sets the
  written array to `top`; the join-with-value refinement is deferred because it
  needs additional `Array.getD`/`set` lemmas. A finer multiplication/division
  and store transfer is later precision work.

- **Conditions are strict.** `BExp.and`/`or` evaluate both operands, so a
  guard-protected partial operation inside a condition
  (`x != 0 && 10 / x > 1`) is not expressible; use the statement-level idiom
  `if (x != 0) { y := 10 / x; }`. This is a language choice (unconditional
  safety obligations), not a missing proof.
- **`entails` is conservative (F1/M3.6).** The interval test certifies constants,
  variables, `+`/`-` with finite endpoint sums, exact `len` for in-support arrays,
  comparisons, and `not`/`and`/`or`; `*`, `/`, and array reads remain `none`. A
  safe program whose assert or divisor needs one of those is rejected, not
  accepted. Extending the test is precision work, not a soundness fix.
- **The v1 `mem` map is optional (F5).** An analyzer that omits it gives every
  array the `top` summary; a read then has no content precision. This is
  precision loss, not unsoundness. The M5 emitter should emit summaries for the
  arrays it reads, and the M4.2 decoder must reject unknown array numbers and
  malformed intervals as specified in `certificate-v1.md` §5.1.
- **T8's generic inclusion half is not yet in the interface.** `Interval.ble_complete`
  is proved for the interval value type, but `bleAbs_complete` (finite-support
  `Abs`) and a `CertDomain.ble_complete` field are absent. M4 must either state
  T8 for the interval instance after proving `bleAbs_complete`, or add a
  completeness field/hypothesis. `check` exists; `encode` is M4, so this is a
  contract decision, not a missing proof of T8.
- **Safety entailment is conservative (M3.6).** The checker's structural
  `exprSafe` predicates are discharged by `entails`, which handles constants,
  variables, `+`/`-`, exact `len`, and comparisons but not multiplication or
  division *inside an assert*. Such programs are rejected, not accepted
  unsoundly. A branch guard's division preconditions are checked via
  `bexpDefined`. `add`/`sub` overflow and division-by-zero/`min/-1` are checked;
  multiplication in a safety-relevant expression is a precision gap, not a
  soundness gap.
- Inclusion is incomplete for octagons (when they exist): the checker may
  reject a valid invariant. See [`NONGOALS.md`](NONGOALS.md).
- Certificates of unsafety are out of scope: the protocol proves safety
  properties, it does not produce counterexample certificates.
- Label partitions are restricted to the finite schemes fixed by the trusted
  semantics; user-supplied partition functions are not accepted (see
  [`certificate-v1.md`](certificate-v1.md), "Open items").
