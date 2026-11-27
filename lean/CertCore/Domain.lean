import CertCore.Semantics

/-!
# `CertCore.Domain` — trusted

The `CertDomain` structure and the generic soundness theorem's interface
(project plan §4.2), plus the `Combinator`/`Encoding` interface of §4.3.

Status: **M2.8 interface, completed for the checker (F1).** The structure now
carries the program's state invariant `P` because a program-specific domain
(interval, with fixed array lengths) cannot make `top_sound` hold for arbitrary
states. `gamma` is a predicate because the Mathlib-free tree has no `Set`.
`transfer` is over `EdgeCmd`, the checker-facing edge action (M1.8/F5), not the
source `Cmd`. The checker's additional needs are carried by the fields below:
`P_step` (the induction invariant), `initOf`/`init_sound` (the base case),
`entails`/`entails_sound` (the safety obligation), and an `Option Abs` for the
certificate's explicit `bot` state (see the note at the end of this file).

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
  /-- `P` is preserved by every edge execution. This is the induction invariant
  T5 needs: the checker knows `P` at the entry, and every step must preserve it. -/
  P_step : ∀ {c : EdgeCmd} {s s' : State},
    P s → EdgeCmd.exec c s = some s' → P s'
  /-- The initial abstract state for a program. -/
  initOf : Program → Abs
  /-- `initOf p` describes the program's initial state, under `P`. -/
  init_sound : ∀ (p : Program), P (State.init p) → gamma (initOf p) (State.init p)
  /-- Safety-predicate entailment: `entails a b = true` means every concrete
  state represented by `a` evaluates `b` to `true` (not `false`, not `none`). -/
  entails : Abs → BExp → Bool
  /-- `entails` is sound for `evalB`. -/
  entails_sound : ∀ {a : Abs} {b : BExp} {s : State},
    entails a b = true → P s → gamma a s → evalB b s = some true

/-! ## Why there is no `bot` field

The v1 certificate's explicit `bot` state is a *coverage* marker, not an abstract
element: the checker should store a point's state as `Option Abs` (`none` = bot)
and skip that point's obligations. A `bot : Abs` field would be unsound to add
naively — with a support-restricted `gamma` such as the interval instance's, an
all-`bot` state satisfies `gamma` vacuously when the support is empty, so it is
not distinguishable from a non-empty state. The `Option` representation makes
"this point is unreachable" a property of the certificate, not of the domain. -/

end CertCore
