/-!
# `CertCore.Proofs` — trusted

Aggregator for the theorem inventory T1–T10 (`docs/THEOREMS.md`).

Status: **stub** (M0). Theorems are added as their milestones close; this
module exists so the axiom audit has a single import root.

The load-bearing theorems are T5 `check_sound` (the kernel), T9 `label_sim`
(path sensitivity as a product), and — post-month — T7 (`reduce_sound`,
`reduce_idem`). T5 must remain a short induction; if it does not, the
semantics is wrong for the purpose.
-/
