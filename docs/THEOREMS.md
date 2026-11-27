# THEOREMS — the theorem contract

Ten theorems. This file is the contract: a status change here is part of the
commit that closes it, and the PR body states the diff (`M3.7: T5 todo →
proved`). Statements are informal here; the Lean statements are authoritative
and live in the file named in the last column.

Status values: `todo` · `in-progress` · `proved` · `post-month`.

| ID | Statement | Role | Difficulty | Status | Milestone | Lean file |
|---|---|---|---|---|---|---|
| **T1** | `step_det : step cfg p s = some c₁ → step cfg p s = some c₂ → c₁ = c₂` (configurations, not just states) | Semantics sanity | Low | **proved** | M1.9 | `Semantics.lean` |
| **T2** | `safe_iff : Safe cfg s ↔ ¬ ∃ n, run cfg n cfg.entry s = none` (no failing prefix exists), with `safe_iff_exists : Safe ↔ ∀ n, ∃ c, run … = some c` | Removes coinduction; every later proof is an ordinary induction on steps | Low | **proved** | M1.10 | `Semantics.lean` |
| **T3** | `run_sound : s ∈ γ a → run n s = some s' → s' ∈ γ (transferStar n a)` | Lifts transfer soundness to traces | Medium | todo | M3 | `Proofs.lean` |
| **T4** | Per domain: `ble_sound`, `join_sound`, `transfer_sound`, `top_sound`, and `entails_sound` for the safety-predicate test | Domain instances; intervals proved | Medium | **proved** (intervals) | M2 + F1 | `Domain/Interval*.lean` |
| **T5** | **`check_sound : D.P (State.init p) → check D p c = .ok → Program.safe p`**, where `Program.safe` requires `Program.WF` | **The kernel theorem** | **Medium** | **proved (M3.7)** | M3.7 | `Proofs.lean` |
| **T6** | Product instance: `ble_sound`, `transfer_sound`, `join_sound` for `D₁ × D₂` | Combinator (a), genericity made executable | Low | todo | M6.2 | `Domain/Product.lean` |
| **T7** | `reduce_sound : γ (ρ (a,b)) ⊆ γ a ∩ γ b` and `reduce_idem : ρ ∘ ρ = ρ` | Reduced product; **post-month** | **High** | post-month | M8 | `Domain/Reduce.lean` |
| **T8** | `encode_accepts : IsPostFixpoint p I → InvariantEntailsSafety p I → check D p (encode p I) = .ok` | Usability / two-sidedness of the contract | Medium | todo | M3/M4 | `Cert.lean` |
| **T9** | `label_sim : step# (s,κ) = some (s',κ') → step s = some s'` (+ converse, errors preserved) | **Path sensitivity as a product** | Medium | todo | M9.3 | `Semantics.lean` |
| **T10** | `decode_sound : decode j = .ok c → WellFormedCert c` (malformed input ⇒ `Diagnostic.malformed`, never a crash) | R4 / adversarial input | Low–Medium | todo | M4.3 | `Cert.lean` |

## Notes on the contract

- **In-month set:** T1–T6, T8–T10. **T7 is post-month (M8)** per
  [roadmap §4.1](../docs/certcore-roadmap.md#L85), which demotes the reduced
  product. Consequences for the write-up, pending a plan amendment: claim **C2**
  is *product-only* in the 4-week artifact, and the plan's "load-bearing three
  are T5, T7, T9" reduces to **T5 and T9**.
- **The load-bearing two in-month** are T5 and T9. T5 must be a short induction
  over a small semantics; if it is not, the semantics is wrong for the purpose
  (gate **G1a**).
- **T8 is what makes the thing usable.** Soundness alone is satisfied by a
  checker that rejects everything; T8 states that every genuine inductive
  invariant has a certificate the checker accepts.
- **T10 is a correctness requirement, not hardening.** A certifying checker has
  an adversarial input model that a verified analyzer does not.
- **T1's statement changed when the semantics did.** The plan's T1 was an
  induction over structured commands and `eval`. M1.6 compiled the AST to a
  deterministic edge machine, so T1 becomes "two successful results from the same
  configuration agree" — immediate, because `step` is a function. The induction
  the plan expected now lives in `eval_det` (M1.5) and in deterministic
  compilation (M1.6); this is recorded here so the narrower statement is visible
  rather than silently swapped.
- **T2's statement also moved.** `Safe` is *defined* in M1.7 as the finite-prefix
  property, so the plan's literal `Safe ↔ ∀ n, run n ≠ none` is `Iff.rfl`. T2 is
  the equivalent formulation the project uses — no fuel has a failing run
  (`¬ ∃ n, run n = none`), plus the finite-prefix form
  (`∀ n, ∃ c, run n = some c`). The induction escape hatch is the definition
  itself: later proofs induct on the step count, never on a coinductive tree.
- **T4 is proved for intervals.** `ble_sound` (M2.3), `join_sound` (M2.4),
  `top_sound` (M2.5), `evalExprAbsOn_sound`/`assignAbsOn_sound` (M2.6/F6; the
  M2.6 `Env` evaluator was removed at F6), the array/instance fields
  (M2.7–M2.8), and `entails_sound` (F1) are all in `Domain/Interval*.lean`.
  T4's status is `proved` for the interval instance; other domains are M6/M7.
- **The checker interface gained three fields at F1.** `CertDomain` now carries
  `initOf`/`init_sound` (the base case), `entails`/`entails_sound` (the safety
  obligations), and `P_step` (the induction invariant). The interval instance
  proves them as `initOf_sound`, `entailsAbs_sound`, and `POn_step`. `entails`
  is conservative: it handles constants, variables, `+`/`-` with finite endpoint
  sums, comparisons, and `not`/`and`/`or`; `*`, `/`, array reads and `len`
  return `false` (declined, not unsound). The `bot` certificate state is
  represented by the checker as `Option Abs` (`none`), not as a `CertDomain`
  field; see the note at the end of `Domain.lean`.
- **Gamma is a predicate, not a `Set`.** Lean core (and this Mathlib-free
  tree) has no `Set` type, so the interval instance exposes
  `Interval.gamma : Interval → I32 → Prop`, and `gamma i v` is the plan's
  `v ∈ γ i`. T4 and later statements use that form.
- **T8 is two-sided only with an entailment hypothesis.** Its inclusion half is
  now proved for intervals: `Interval.ble_complete` (F4) says semantic inclusion
  implies `ble a b = true`. The `i32Min`/`i32Max` endpoint cases in
  `leLo`/`leHi` are what make it complete: `some i32Min` is an effective `-∞`
  lower bound and `some i32Max` an effective `+∞` upper bound, because no `I32`
  lies outside them. The safety half of T8 cannot hold for an incomplete
  `entails`; the statement therefore carries an explicit
  `InvariantEntailsSafety` hypothesis (or must restrict to predicates the test
  decides exactly). T8 itself is still M3/M4, where `check`/`encode` exist.
- **T8's inclusion half is not yet generic over `CertDomain`.** What is proved is
  `Interval.ble_complete` for the interval value type. `bleAbs_complete` for the
  finite-support `Abs`, and a `ble_complete` field in `CertDomain`, are not yet
  present. M3.1 must either state T8 for the interval instance after proving
  `bleAbs_complete`, or add a completeness field/hypothesis to `CertDomain`.
  The T8 row is a contract placeholder until that decision; `check` and `encode`
  do not exist yet.
- **T5's conclusion is `Program.safe`, which includes `Program.WF`.** A malformed
  source program has no meaning and is never certified safe; M3's checker must
  establish the decidable source contract (`checkWF`: dense unique points,
  declared arrays within resource bounds, assigned reads) before returning `.ok`.
- **T4 carries one operation the plan's sketch omits.** Safety cannot be a `ble`
  call (`{x ≠ 0}` is not one interval), so each domain supplies a sound
  entailment test for safety predicates. This was settled at F1:
  `entails : Abs → BExp → Bool` with
  `entails_sound : entails a b = true → P s → gamma a s → evalB b s = some true`
  (truth *and* definedness). The interval test's shape and its conservative
  cases are in [`certificate-v1.md` §12.6](certificate-v1.md).
- **`Program.compile_wf` is a TCB well-formedness lemma, not a numbered theorem.**
  It proves `CFG.WF (Program.compile p)`: the entry is inside the instruction
  array, and every instruction the machine can fetch sends control to a point
  inside the array. T5 uses this to rule out a "missing instruction" failure
  that no certificate can discharge. It lives in `Semantics.lean` and is
  exercised by `Tests/Compile.lean`.
- **Source WF is a decidable contract, not a numbered theorem.**
  `Program.checkWF` checks dense unique points, declared array indices, assigned
  reads, and a bounded `maxPoint`; `Program.compileChecked` returns `none` for a
  malformed program instead of compiling it. `Cmd.compile` itself takes a size
  bound and a proof-carrying `place`, so an out-of-range write is not
  representable. `Tests/Compile.lean` pins accepted and rejected shapes.
- **`step_edge` is the operational/edge bridge, not a numbered theorem.** It
  states that every successful `step` corresponds to an edge in `cfg.edges`
  whose `EdgeCmd.exec` effect produces the same state. This is what lets T5
  turn an edge-indexed obligation into a fact about the transition `step`
  actually took. It lives in `Semantics.lean` and is exercised by
  `Tests/Edges.lean`.
- **No theorem ships with `sorry`.** If a lemma must be deferred, it goes in
  [`known-gaps.md`](known-gaps.md) and the branch does not merge.
- The audit command and its expected footprint are in [`TCB.md`](TCB.md).
