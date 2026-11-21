/-!
# `CertCore.Semantics` — trusted

Abstract syntax, configurations, the fuel-indexed deterministic small-step
semantics, and the safety predicate `Safe`.

Status: **stub** (M0). Filled in by M1. This module is inside the TCB: a bug
here changes what "safe" means (project plan §10.1).

Planned contents:

* `I32` — bounded 32-bit integers with *observable* wrap-around (M1.1).
  Overflow must be a safety violation, not impossible by construction.
* `Expr`, `Cmd`, `Program` with labelled program points (M1.2–M1.3).
* `State` — total environment and memory, so the semantics never gets stuck
  on a missing variable (M1.4).
* `eval` — `none` for division by zero, overflow, and out-of-bounds read.
  This is where the safety property is *defined* (M1.5).
* `step`, `run`, `Safe` — `Safe s := ∀ n, run n s ≠ none`, no coinduction
  (M1.6–M1.7).
* `edges` — the CFG that the checker's obligations are indexed by (M1.8).
* T1 `step_det` (M1.9), T2 `safe_iff` (M1.10).
-/
