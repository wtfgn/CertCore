/-!
# `CertCore.Proofs` — trusted

Aggregator for the theorem inventory T1–T10 (`docs/THEOREMS.md`).

Status: **aggregator stub.** T1/T2 live in `Semantics.lean`; this module will
collect the later theorem statements as milestones close. The M1 audit imports
`Semantics` directly.

The load-bearing theorems are T5 `check_sound` (the kernel), T9 `label_sim`
(path sensitivity as a product), and — post-month — T7 (`reduce_sound`,
`reduce_idem`). T5 must remain a short induction; if it does not, the
semantics is wrong for the purpose.
-/
