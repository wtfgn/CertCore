/-!
# `CertCore.Domain` — trusted

The `CertDomain` structure and the generic soundness theorem's interface
(project plan §4.2), plus the `Combinator`/`Encoding` interface of §4.3.

Status: **stub** (M0). Filled in by M2 (interval instance) and M3 (kernel).

Everything in the trusted tree is generic over `CertDomain`; the kernel never
sees a fixpoint, a widening, or a heuristic. Two design decisions matter:

* `ble : Abs → Abs → Bool` with a reflection lemma `ble_sound`, rather than
  `Decidable` everywhere, so the checker compiles to a predictable cost model
  (project plan D7).
* The certificate is an *inductive invariant*: a map from program points to
  abstract states, not a fixpoint trace.

Planned contents:

* `CertDomain` structure: `Abs`, `gamma`, `ble`, `ble_sound`, `top`,
  `top_sound`, `transfer`, `transfer_sound`, `join`, `join_sound`.
* `Interval` instance (`CertCore/Domain/Interval.lean`, M2).
* Product instance (M6) and reduced product combinator (post-month, M8).
-/
