import CertCore.Semantics

/-!
# `CertCore.Domain` — trusted

The `CertDomain` structure and the generic soundness theorem's interface
(project plan §4.2), plus the `Combinator`/`Encoding` interface of §4.3.

Status: **M2.8 interface.** The structure now carries the program's state
invariant `P` because a program-specific domain (interval, with fixed array
lengths) cannot make `top_sound` hold for arbitrary states. `gamma` is a
predicate because the Mathlib-free tree has no `Set`. `transfer` is over
`EdgeCmd`, the checker-facing edge action (M1.8/F5), not the source `Cmd`.

Everything in the trusted tree is generic over `CertDomain`; the kernel never
sees a fixpoint, a widening, or a heuristic. Two design decisions matter:

* `ble : Abs → Abs → Bool` with a reflection lemma `ble_sound`, rather than
  `Decidable` everywhere, so the checker compiles to a predictable cost model
  (project plan D7).
* The certificate is an *inductive invariant*: a map from program points to
  abstract states, not a fixpoint trace.
-/

namespace CertCore

/-- A certificate domain, parameterised by the program's concrete-state
invariant `P`. `P` is needed for program-specific facts such as fixed array
lengths; `top_sound` and `transfer_sound` only claim their result for states
satisfying it. -/
structure CertDomain where
  /-- The concrete states the program can be in (e.g. array lengths fixed). -/
  P : State → Prop
  /-- Abstract states. -/
  Abs : Type
  /-- Concretisation: `gamma a s` means `s` is described by `a`. -/
  gamma : Abs → State → Prop
  /-- Executable inclusion test. -/
  ble : Abs → Abs → Bool
  /-- `ble` reflects inclusion on program states. -/
  ble_sound : ∀ {a b : Abs} {s : State},
    ble a b = true → P s → gamma a s → gamma b s
  /-- The no-information abstract element. -/
  top : Abs
  /-- `top` describes every program state. -/
  top_sound : ∀ {s : State}, P s → gamma top s
  /-- Transfer over a checker edge. -/
  transfer : EdgeCmd → Abs → Abs
  /-- Transfer is sound for every successful edge execution. -/
  transfer_sound : ∀ {c : EdgeCmd} {a : Abs} {s s' : State},
    P s → gamma a s → EdgeCmd.exec c s = some s' →
    P s' → gamma (transfer c a) s'
  /-- Join (least upper bound). -/
  join : Abs → Abs → Abs
  /-- Join contains both operands. -/
  join_sound : ∀ {a b : Abs} {s : State},
    P s → gamma a s ∨ gamma b s → gamma (join a b) s

end CertCore
