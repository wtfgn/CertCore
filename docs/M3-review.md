# CertCore — Interim Review at M3

| | |
|---|---|
| Reviewed | 2026-11-27 |
| Milestone | **M3 — checker and T5** |
| Branch / commit | `feat/checker` @ `b5494e5` (`M3.8–M3.9: audit and golden accept`) |
| Build | `lake build` green, 31 jobs, no warnings |
| Tests | 28/28 green: M1/M2 suite plus `Certificate`, `Diagnostic`, `CheckSkeleton`, `CheckInit`, `CheckEdges`, `CheckSafety`, `Golden` |
| `sorry` | none in `lean/` |
| Axioms | `check_sound`: `[propext, Quot.sound]`; full `Audit.lean` clean |
| Merge state | 8 commits ahead of `main` (`7a2856f`, M2); not merged, not pushed |
| Verdict | **The checker is sound and T5 is genuinely closed, but M3 was not cost-complete or v1-conformant at the reviewed commit.** The sparse-map representation made every lookup linear, `wellFormed` was quadratic and recompiled the program per state, and a certificate state at the halt point was accepted despite v1 §3.1. The post-review commits fix those two and restrict M3 to the flat one-label scheme; only the accepted `hP` premise and a scaling test remain. |

> **Post-review fixes.** M3-F1 and M3-F4 are fixed. `Certificate` now stores a
> row-major `Array (Option (Option Abs))`, `cellAt`/`lookup?` are O(1),
> `wellFormed` checks the array length / entry cell / empty halt row without a
> per-state `Program.compile` or `eraseDups`, and a state at the halt point is
> rejected. M3-F3 is resolved by **restricting M3 to `labels = 1`**; branch
> history stays M9.3. The M3 tests were updated; the non-WF source,
> halt-state, labels-two rejection and corrupted-golden tests were added.
> `M3-F5` and the `M3-F7` status lines were corrected. `M3-F6` now has the
> label test; a scaling benchmark remains. Build is green, 28/28 tests pass, and
> `check_sound` remains `[propext, Quot.sound]`. The findings below describe the
> reviewed commit `b5494e5`; the post-fix verification is in §8.

This review is based on reading every new M3 source and test file, re-reading
`certificate-v1.md`, `THEOREMS.md`, `known-gaps.md` and the M3 roadmap, building
the tree, running all 28 test files, printing `#print axioms check_sound`, and
reproducing the halt-state and cost findings with small `#eval` programs. No
Lean source file was changed while writing this review; this document and the
README docs-index entry are the only additions.

---

## 0. Executive summary

- **T5 is real.** `check_sound` is proved for an arbitrary `CertDomain`, with the
  approved `hP : D.P (State.init p)` base-case premise. The proof decomposes the
  checker, proves the init/edge/safety projections, connects `entails` to
  successful steps, and runs the invariant induction. Its axiom footprint is
  `[propext, Quot.sound]`; there is no `Classical.choice`, no `sorryAx`, and the
  division lemma `div?_some_of_safe` is part of the audited footprint.
- **The three obligation families are implemented and tested.** The checker
  derives init, edge and safety obligations from the program, returns typed
  diagnostics, and the golden test accepts a program with an assert and a
  non-singleton division.
- **The checker is not linear.** `Certificate` stores states as a `List` and
  `lookup?` is a linear `List.find?`; every init/edge/safety obligation performs
  a fresh linear lookup. `wellFormed` additionally calls `Program.compile p`
  inside the per-state `all` lambda and checks duplicates with `eraseDups`, so
  shape validation is quadratic before any obligation runs. This contradicts the
  cost model in `certificate-v1.md` §9 and the T10/R4 "no super-linear work"
  requirement.
- **A certificate state at the halt point is accepted.** v1 §3.1 says the halt
  point carries no certificate state. `Certificate.wellFormed` only requires
  `point < instrs.size`, and the halt point is `instrs.size - 1`. I reproduced
  `wellFormed = true` and `check = .ok` with a state at the halt point.
- **The label contract is narrower than the certificate type.** `labels` may be
  up to 64, but the M3.5 edge loop uses the identity successor label. v1's
  `branch-history` scheme updates the label at a branch; M9.3 is where that
  arrives. For the unlabelled `Program.safe` theorem this is sound, but the
  checker does not validate the labeled protocol the format describes.
- **T5's contract changed.** The original theorem row was
  `check D p c = .ok → Program.safe p`; the implemented theorem has an extra
  `hP` premise. The premise is honest and was approved, but it must be treated
  as part of the T5 contract, not as an implementation detail.
- **Documentation drift is now material.** `Check.lean` still says "Status:
  M3.6"; `Cert.lean` still says "No check/decode yet"; `known-gaps.md` says
  `len` returns `false` (M3.6 made it exact) and that division inside a
  condition is rejected (a branch division guard is accepted; an assert with
  division is rejected). `README` still prints the M2 CLI banner.

**Bottom line.** M3 crosses the hard milestone: the kernel theorem is proved,
the checker rejects bad certificates with values, and the golden test proves the
end-to-end path. Do not merge it as the finished cost story. The sparse-map
representation must become indexed before the cost claims and T10 are credible;
the halt-state rule is a small, concrete v1 fix. The label and `hP` decisions
should be written down before M4 builds the decoder around this representation.

---

## 1. What M3 actually delivers

| Roadmap item | Delivered | Evidence |
|---|---|---|
| M3.1 certificate type | `StateAt`/`Certificate`, `Option Abs` bot marker, sparse list, lookup helpers | `Cert.lean` |
| M3.2 diagnostic | `Obligation`, `Diagnostic Abs`, `CheckResult`, constructors for malformed/unsupported/hash/init/edge/safety | `Check.lean` |
| M3.3 skeleton | `check : CertDomain → Program → Certificate D.Abs → CheckResult D.Abs Unit`, shape validation, total failure path | `Check.lean`, `CheckSkeleton.lean` |
| M3.4 init | `ble (initOf p) (at entry)` for every entry label; explicit bot rejected | `CheckInit.lean` |
| M3.5 edge | `ble (transfer e.cmd (at src)) (at dst)` for every CFG edge and label | `CheckEdges.lean` |
| M3.6 safety | Structural `exprSafe`/`bexpDefined`/`instrSafe`, per-point `entails`, division/overflow/branch/array coverage | `CheckSafety.lean` |
| M3.7 T5 | `check_sound` with `hP`, division lemma, `CertInv` run invariant | `Proofs.lean`, `Golden.lean` |
| M3.8 audit | `check_sound` printed by `Audit.lean`; CI grep remains | `Audit.lean`, CI |
| M3.9 golden | `x := 4; y := 8 / x; assert y = 2` accepted; `check_sound` derives `Program.safe` | `Golden.lean` |

The roadmap's M3.1 text still mentions per-edge successor states and assertion
states. They are **not** in the type; this is the v1 §10 deletion, and the
implementation follows the frozen format rather than the older sketch. That is
defensible, but the roadmap and the type comment should say so explicitly.

---

## 2. Strengths

1. **The checked interface is small and typed.** A rejection carries an
   obligation kind, point/label, edge, expected/actual abstract states and
   decoder detail; no verdict is a string.
2. **The sparse-map semantics are explicit.** `lookup?` distinguishes
   `some (some a)`, `some none` (bot) and `none` (missing = top). That is the
   right distinction for v1, and the tests pin all three outcomes.
3. **Safety is structural, not certificate-supplied.** `exprSafe` and
   `bexpDefined` are derived from `Expr`/`BExp`; a certificate cannot assert its
   own safety predicate.
4. **Division safety is full, not the conservative fallback.** The `min / −1`
   exclusion and the `Int.tdiv` bounds are proved in `div?_some_of_safe`; the
   golden and safety tests exercise division.
5. **T5's decomposition is readable.** `check_parts`, the three obligation
   projections, `exprSafe_sound`, `instrSafe_step`, `run_inv` and
   `check_sound` each have a clear role. The proof is long but not circular.
6. **The audit is meaningful.** `check_sound` is clean and the division lemma is
   in the same footprint; the CI gate is not just printing an unrelated M1
   sample.

---

## 3. Findings

### M3-F1 (High) — the checker is super-linear, despite the stated cost model

The trusted data structure is a list:

```lean
structure Certificate (Abs : Type) where
  labels : Nat
  entry : StateAt Abs
  states : List (StateAt Abs)
```

and lookup is a linear search:

```lean
def find? ... := c.states.find? (fun s => keyMatches s p l)
```

`Certificate.stateAt` calls `lookup?`; every init/edge/safety obligation calls
`stateAt`/`stateAtEntry`. If `N = |states|`, `P = |points|`, `K = labels` and
`E = |edges|`:

- init: `K` lookups, `O(K·N)`;
- edges: `E·K` obligations, each with a source and target lookup, `O(E·K·N)`;
- safety: `P·K` obligations, each with a lookup, `O(P·K·N)`;
- with `E = O(P)` and `N = O(P·K)`, this is `O(P²·K²)` work, not
  `O((E+P)·K)`.

The shape check makes it worse:

```lean
c.states.all (fun s =>
  Nat.blt s.label c.labels &&
  Nat.blt s.point (Program.compile p).instrs.size)
...
(c.keys.eraseDups.length == c.keys.length)
!(c.keys.elem (c.entry.point, c.entry.label))
```

`Program.compile p` is **inside the lambda**, so it is called once per state;
`eraseDups` and `elem` make duplicate/entry checks quadratic. Shape validation
is therefore `O(N·P + N²)` before the obligations start. `eraseDups` and
`elem` also allocate and traverse maps of the whole state list.

Why this matters:

- `certificate-v1.md` §9 promises `O(S)` decode, `O(P·K)` indexing,
  `O((E+P)·K)` obligations and `O(P·K)` memory.
- R4/T10 promises malformed input cannot induce super-linear work.
- The north-star measurement (C4) compares certificate size and checker time;
  a quadratic checker makes the frontier meaningless and lets a hostile
  certificate DoS the kernel.

This is not a proof-soundness bug; it is a cost-contract bug. It is also the one
finding that should be fixed before M4, because the decoder's output type and
the checker's index should be chosen together.

**Recommendation.** Store an indexed representation in the trusted type (for
example `Array (Option (Option Abs))` at `point*K + label`, or a sorted array
with binary search), build it once in `check`/the decoder, and make duplicate,
range and entry checks O(N) or O(N log N). Keep the list only as an encoder/decoder
intermediate. Add a small scaling benchmark: 2× states should not 4× lookup
time.

### M3-F2 (Medium) — T5 has an extra `hP` premise; it is now part of the contract

The theorem table originally stated:

```lean
check_sound : check D p c = .ok → Program.safe p
```

The implemented theorem is:

```lean
check_sound (hP : D.P (State.init p)) (h : check D p cert = .ok) :
  Program.safe p
```

This is honest: a generic `CertDomain` has no proof of its own `P` at the
program's initial state, and the interval instance only proves
`POn_init` for canonical `lengths`. The user approved the premise and the
`THEOREMS.md` row was updated. But it changes what "the checker proves safety"
means for callers: acceptance is conditional on an externally supplied domain
fact.

**Recommendation.** Record the premise in `THEOREMS.md` (done), in
`docs/TCB.md`, and in the M4 parser/caller contract. Either add a
`P_init`/program-parameterised domain field later or show every canonical caller
discharges `hP`. Do not let a future caller assume `check_sound` is
unconditional.

### M3-F3 (Medium) — `labels` are checked with the identity update, not v1 branch history

`Certificate.wellFormed` allows `1 ≤ labels ≤ 64`, and `checkEdgeLabels` loops
over every label. But the successor is always the same label:

```lean
match cert.stateAtEntry D e.dst l with
```

There is no `labelStep`/`branch-history` update. `Check.lean` says so, and M9.3
owns the real successor function. For the M3 semantics this is sound:
`Program.safe` is unlabelled, and T5 uses `cert.entry.label` as the invariant
label. It is **not** a check of the labeled protocol in v1 §6.

**Recommendation.** Before M4, decide one of:

- restrict M3 certificates to `labels = 1` (the flat `none` scheme) and reject
  larger label counts as unsupported until M9; or
- add the `labels` descriptor and the `branch-history` update now, and make the
  edge obligation use `labelStep`.

Either way, document that a multi-label M3 certificate is not branch-sensitive.
`CheckEdges.twoLabels` currently tests two identity labels, not branch history.

### M3-F4 (Medium) — a certificate state at the halt point is accepted

v1 §3.1: the halt point "carries no certificate state". `wellFormed` checks:

```lean
Nat.blt s.point (Program.compile p).instrs.size
```

The halt point is `instrs.size - 1`, so it passes. Reproduction with
`p := skip 0` and a state at point `1`:

```text
haltCert.wellFormed p0 = true
(check D p0 haltCert).isOk = true
(Program.compile p0).instrs.size = 2
```

This does not make `Program.safe` false, but it is a v1 conformance bug: the
decoder and checker would accept a certificate field the format calls malformed,
and an encoder could emit an ignored state that inflates the measured
certificate size.

**Recommendation.** Require `point < instrs.size - 1` for `states` (entry point
is `p.entry`, already a source point), add a test, and mirror the rule in M4.2.

### M3-F5 (Medium) — safety documentation contradicts the implemented precision

`known-gaps.md` says:

- "`*`, `/`, array reads, and `len` return `false`" — **false for `len`**:
  M3.6 extended `evalExprGuarded` with exact `len` and `entails` proves
  `i < len a`.
- "division inside a condition/assert expression" is rejected. A **branch**
  division guard is accepted: `CheckSafety.lean` has

  ```lean
  #guard D.entails (st1 1) (instrSafe (.branch divGuard 1 2))
  ```

  because `bexpDefined` uses `exprSafe`, including the division preconditions.
  An **assert** `assert (10/x == ...)` is still rejected because
  `atomicSafe (.assert b) = b` and `entails` cannot evaluate the division.

`Check.lean` repeats the "multiplication and division inside conditions" claim
in its M3.6 module comment. The implementation is sound and conservative in the
remaining cases, but the docs overstate the restriction.

**Recommendation.** Update `known-gaps.md` and the `Check.lean` comment to say:
`len` is exact when in support; multiplication and array reads in a
safety-relevant expression are rejected; division is checked in assignment RHS
and branch guards but rejected inside an assert. Add a test for an assert with
division if that distinction is intended.

### M3-F6 (Medium) — tests miss the cases the new code is most likely to get wrong

The suite is good on individual obligations, but it does not cover:

- a **non-`Program.WF`** program being rejected before certificate validation;
- a **halt-point state** (the reproduction above);
- a **single end-to-end corrupted golden certificate** with a sensible
  diagnostic (the exit criterion says one hand-corrupted certificate; the
  individual `CheckInit`/`CheckEdges`/`CheckSafety` tests are close but not the
  same path);
- **branch-history labels** (not implemented; at least a rejection test if
  M3 is restricted to the flat scheme);
- **`hP` absent / a noncanonical interval instance**, so the T5 premise is not
  silently assumed;
- **cost/scaling** (not a unit test, but at least a benchmark guard).

**Recommendation.** Add the first four as Lean tests; add a small cost
regression in M4/M10. The golden test should include a `golden_reject` variant
with one corrupted state.

### M3-F7 (Low) — status and command documentation are stale

- `Check.lean` line 10 says "Status: M3.6 ... T5 is M3.7"; the file is the final
  checker and T5 is committed.
- `Cert.lean` line 22 says "No `check`/`decode` yet"; `check` exists.
- `README.md` quick-start still prints
  `certcore 0.1.0 (M2 interval domain; checker not implemented yet)`.
- `known-gaps.md` line 12 still calls T8 a "pending M3.1 contract decision";
  M3.1 has passed and the decision moved to M4.
- `THEOREMS.md` still lists T3 (`run_sound`) as `todo` with milestone M3, but
  M3 did not implement it; T5 used its own run invariant instead.

None of these affect soundness; they matter because the review/audit trail is
part of the deliverable.

### M3-F8 (Low) — `wellFormed` is doing two jobs

`Certificate.wellFormed` checks the **certificate** shape and also depends on
the **program** (`p.entry`, `Program.compile p`), including compiling it inside
the state predicate. That couples a generic certificate type to the frontend and
makes the decoder/checker contract harder to test in isolation. It is not wrong,
but it is the reason shape validation is expensive and why the halt rule is easy
to miss.

**Recommendation.** Split the bounds check into a program-parameterised
`ShapeWF p cert` (with a precomputed instruction-count argument) and a small
program-independent key-uniqueness check. The checker can build both once; the
tests can target each.

---

## 4. Reproductions

### 4.1 Halt-point state accepted

Input:

```lean
p0 := { body := .skip 0, arrays := #[] }
D  := intervalDomain (fun _ => 0) ["x"] []
cert := {
  labels := 1,
  entry := { point := 0, label := 0, state := some (D.initOf p0) },
  states := [ { point := 1, label := 0, state := some top } ] }
```

Output:

```text
haltCert.wellFormed p0 = true
(check D p0 haltCert).isOk = true
(Program.compile p0).instrs.size = 2
```

`point = 1` is the halt point. v1 §3.1 says it must not carry a state.

### 4.2 Branch division is accepted, assert division is not

`CheckSafety.lean`:

```lean
def divGuard : BExp := .cmp .lt (.div (.const (c 10)) (.var "x")) (.const (c 3))

#guard D.entails (st1 1) (instrSafe (.branch divGuard 1 2))
#guard !D.entails (st1 0) (instrSafe (.branch divGuard 1 2))
```

The first passes, so `known-gaps.md`'s blanket "division inside a condition" is
too strong. The branch guard is checked for definedness; the argument to
`assert` is checked for truth and is still rejected because `entails` cannot
evaluate division.

### 4.3 Cost path

For `N` states, `checkInit`, `checkEdges` and `checkSafety` all reach
`Certificate.lookup?` → `List.find?`. `wellFormed` reaches
`Program.compile p` inside `c.states.all` and `c.keys.eraseDups`. The code path
is direct; no benchmark is needed to see the asymptotic difference from §9.

---

## 5. What is not a bug

- **No soundness hole found in T5.** `check_sound` is proved, `exprSafe_sound`
  covers division and read bounds, `instrSafe_step` covers atomic and branch
  steps, and `run_inv` uses `step_edge`, `transfer_sound`, `ble_sound`,
  `entails_sound` and `P_step`. The audit is clean.
- **`bot` vs missing is correct.** `some none` is a coverage marker; `none` is
  `top`; the checker skips bot and rejects a reachable edge into bot. This is
  the intended v1 behavior.
- **Missing `successors`/`assertions` fields are intentional.** v1 §10 dropped
  them; the certificate supplies states only. The roadmap's older M3.1 text
  should be corrected, not the type.
- **Conservative multiplication / assert-division is a precision limit, not a
  soundness bug.** The checker rejects programs rather than accepting them
  unsoundly; the docs only need to say exactly which cases are rejected.
- **The T5 `hP` premise is honest.** It is not a missing proof hidden with an
  axiom; it is a caller obligation, and the interval instance discharges it for
  the canonical lengths.

---

## 6. Recommended order before merge/M4

1. **Fix M3-F1 first.** Choose the indexed certificate representation and make
   `wellFormed` O(N) or O(N log N). This is the only finding that changes the
   M4 decoder's output type; doing it after M4 would duplicate work.
2. **Fix M3-F4.** Reject states at the halt point; add a test.
3. **Settle M3-F3.** Restrict M3 to the flat `labels = 1` scheme or implement
   branch-history now. Do not leave a multi-label certificate looking validated
   when only identity labels are checked.
4. **Update the contract docs (M3-F2/F5/F7):** `hP`, the exact safety precision,
   `len`, stale status lines, and the T8/T3 ownership.
5. **Add the missing tests (M3-F6):** non-WF rejection, halt state, end-to-end
   corrupt golden, and the label restriction.
6. Re-run build, 28+ tests, `sorry` gate and audit; then merge M3.

If the project wants to keep M3 unmerged while M4 starts, the decoder should be
designed against the **indexed** type, not the current list, so M4 does not have
to redo the interface.

---

## 7. Review method

- Read `Cert.lean`, `Check.lean`, `Proofs.lean`, `Domain.lean`, the interval
  instance, `Audit.lean`, all seven M3 test files, `certificate-v1.md`,
  `THEOREMS.md`, `known-gaps.md`, `TCB.md` and the M3 roadmap.
- `lake build` (31 jobs), all 28 tests, the `sorry` gate and `Audit.lean`.
- `#print axioms check_sound` and the helper lemmas used by T5.
- Reproduced the halt-state acceptance with `#eval` and checked the branch
  division guard against the safety test.
- The original snapshot made no Lean source change. The post-review fixes in
  §8 were applied afterwards; they are not part of the reviewed `b5494e5`
  snapshot.

---

## 8. Post-review fix status

Applied in the post-review fix commits (not part of the `b5494e5` snapshot):

| Finding | Status | Change |
|---|---|---|
| M3-F1 | **fixed** | Row-major `Array` certificate; O(1) `cellAt`/`lookup?`; `wellFormed` checks length, entry cell and halt row in O(1)+O(labels); no per-state `compile` or `eraseDups` |
| M3-F2 | open (accepted contract) | `hP` remains a T5 premise; documented in `THEOREMS.md` and `Proofs.lean` |
| M3-F3 | **fixed (restriction)** | `wellFormed` requires `labels = 1`; multi-label/branch-history certificates are rejected until M9.3 |
| M3-F4 | **fixed** | `haltRowEmpty` rejects every label's halt cell; `CheckSkeleton` has a regression test |
| M3-F5 | **fixed (docs)** | `known-gaps` now says exact `len`, branch-guard division, and assert-division precision correctly; `Check.lean` comment updated |
| M3-F6 | partially fixed | added non-WF, halt-state, labels-two rejection and corrupted-golden tests; a scaling benchmark remains |
| M3-F7 | partially fixed | `Check.lean`/`Cert.lean` status, CLI banner and `known-gaps` T8 owner updated; `THEOREMS` T3 ownership still needs a decision |

Verification of the worktree:

| Check | Result |
|---|---|
| `lake build` | 31 jobs, no warnings |
| Tests | 28/28 |
| `sorry` | none |
| `#print axioms check_sound` | `[propext, Quot.sound]` |
| `Audit.lean` | clean |

The remaining merge blockers are therefore **M3-F2** (record the accepted
`hP` premise) and **M3-F6**'s scaling benchmark. M3-F1, M3-F3 and M3-F4 are no
longer blockers.
