# THEOREMS — the theorem contract

Ten theorems. This file is the contract: a status change here is part of the
commit that closes it, and the PR body states the diff (`M3.7: T5 todo →
proved`). Statements are informal here; the Lean statements are authoritative
and live in the file named in the last column.

Status values: `todo` · `in-progress` · `proved` · `post-month`.

| ID | Statement | Role | Difficulty | Status | Milestone | Lean file |
|---|---|---|---|---|---|---|
| **T1** | `step_det : step c s = some s' → step c s = some s'' → s' = s''` | Semantics sanity | Low | todo | M1.9 | `Semantics.lean` |
| **T2** | `safe_iff : Safe s ↔ ∀ n, run n s ≠ none` | Removes coinduction; every later proof is an ordinary induction | Low | todo | M1.10 | `Semantics.lean` |
| **T3** | `run_sound : s ∈ γ a → run n s = some s' → s' ∈ γ (transferStar n a)` | Lifts transfer soundness to traces | Medium | todo | M3 | `Proofs.lean` |
| **T4** | Per domain: `ble_sound`, `join_sound`, `transfer_sound`, `top_sound`, and `entails_sound` for the safety-predicate test | Domain instances; intervals in-month | Medium | todo | M2 | `Domain/Interval.lean` |
| **T5** | **`check_sound : check D p c = .ok → Safe p`** | **The kernel theorem** | **Medium** | todo | M3.7 | `Check.lean` |
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
- **T4 carries one operation the plan's sketch omits.** Safety cannot be a `ble`
  call (`{x ≠ 0}` is not one interval), so each domain supplies a sound
  entailment test for safety predicates. Rationale and consequences are in
  [`certificate-v1.md` §12.6](certificate-v1.md); settle the exact interface
  before M2.6.
- **No theorem ships with `sorry`.** If a lemma must be deferred, it goes in
  [`known-gaps.md`](known-gaps.md) and the branch does not merge.
- The audit command and its expected footprint are in [`TCB.md`](TCB.md).
