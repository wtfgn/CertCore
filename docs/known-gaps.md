# known-gaps

Anything in the trusted tree that is not proved, or is proved only under a
stated limitation, is recorded here. `main` never carries an undocumented gap
(roadmap §2, rule 5).

Format: one row per gap, with the lemma/theorem it blocks, the milestone that
owns it, and whether it is a *deferral* (planned) or a *limitation* (won't fix).

| # | Gap | Blocks | Owner | Kind | Resolution |
|---|---|---|---|---|---|
| — | *(none yet — the M0 tree contains no proofs and no `sorry`)* | — | — | — | — |

## Standing limitations (not gaps)

These are true by design and will be documented in the write-up rather than
fixed:

- Inclusion is incomplete for octagons (when they exist): the checker may
  reject a valid invariant. See [`NONGOALS.md`](NONGOALS.md).
- Certificates of unsafety are out of scope: the protocol proves safety
  properties, it does not produce counterexample certificates.
- Label partitions are restricted to the finite schemes fixed by the trusted
  semantics; user-supplied partition functions are not accepted (see
  [`certificate-v1.md`](certificate-v1.md), "Open items").
