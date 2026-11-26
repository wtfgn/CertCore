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
| **T4** | Per domain: `ble_sound`, `join_sound`, `transfer_sound`, `top_sound`, and `entails_sound` for the safety-predicate test | Domain instances; intervals in-month | Medium | **in-progress** | M2 | `Domain/Interval.lean` |
| **T5** | **`check_sound : check D p c = .ok → Program.safe p`**, where `Program.safe` requires `Program.WF` | **The kernel theorem** | **Medium** | todo | M3.7 | `Check.lean` |
| **T6** | Product instance: `ble_sound`, `transfer_sound`, `join_sound` for `D₁ × D₂` | Combinator (a), genericity made executable | Low | todo | M6.2 | `Domain/Product.lean` |
| **T7** | `reduce_sound : γ (ρ (a,b)) ⊆ γ a ∩ γ b` and `reduce_idem : ρ ∘ ρ = ρ` | Reduced product; **post-month** | **High** | post-month | M8 | `Domain/Reduce.lean` |
| **T8** | `encode_accepts : IsPostFixpoint p I → check D p (encode p I) = .ok` | Usability / two-sidedness of the contract | Medium | todo | M3 | `Cert.lean` |
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
- **T4 is landing in pieces during M2.** **T4a `ble_sound`** is proved at
  M2.3; **T4b `join_sound`** is proved at M2.4; **T4c `transfer_sound`** is
  M2.6, with `top_sound` and `entails_sound` at M2.5–M2.6.
- **Gamma is a predicate, not a `Set`.** Lean core (and this Mathlib-free
  tree) has no `Set` type, so the interval instance exposes
  `Interval.gamma : Interval → I32 → Prop`, and `gamma i v` is the plan's
  `v ∈ γ i`. T4 and later statements use that form.
- **T5's conclusion is `Program.safe`, which includes `Program.WF`.** A malformed
  source program has no meaning and is never certified safe; M3's checker must
  establish the decidable source contract (`checkWF`: dense unique points,
  declared arrays within resource bounds, assigned reads) before returning `.ok`.
- **T4 carries one operation the plan's sketch omits.** Safety cannot be a `ble`
  call (`{x ≠ 0}` is not one interval), so each domain supplies a sound
  entailment test for safety predicates. Rationale and consequences are in
  [`certificate-v1.md` §12.6](certificate-v1.md); settle the exact interface
  before M2.6.
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
