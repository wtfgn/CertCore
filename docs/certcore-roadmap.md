# CertCore — Execution Roadmap

**Milestones, feature branches, and subtasks.**

| | |
|---|---|
| Companion to | `certcore-project-plan.md` (the *what* and *why*; this is the *when* and *in what order*) |
| Horizon | 20 working days + 2 days prep, 4 weeks, 4 gates, 1 ship date |
| Budget | Prep window: 4 ½d. Main window: 40 ½d, of which **38 named work + 2 buffer** |
| Unit | `½d` = half a working day. `0.25` is an hour or two |
| Branch rule | **One branch per feature.** A feature is a coherent, independently mergeable unit that leaves `main` green. Subtasks are *commits* on that branch |

---

## 1. How to read this

Each milestone has five parts: a goal, the branch(es) it ships on, a table of subtasks, exit criteria, and the gate it feeds. Subtask IDs (`M3.7`) go in commit messages and PR bodies, so that three weeks later `THEOREMS.md` can point back at the work that produced each theorem.

Estimates assume a competent Lean user who has done the week-0 prep. They are not commitments; they are the numbers the budget in §9 is built from, and that budget closes to **exactly** 40 ½d. If a subtask overruns by more than 2×, stop and use §10 rather than pushing through.

---

## 2. Branch and merge model

**Why not one branch per subtask.** Sixty branches, each half-finished, none of which builds — that is how a month disappears into merge conflicts. A branch must be a state someone could merge, and `main` must stay green: `lake build` succeeds, the axiom audit is clean, the golden tests pass. So the branch is the *feature*; the subtask is the *commit*.

**Naming.**

| Prefix | Use | Merges? |
|---|---|---|
| `chore/` | build, CI, toolchain, repo hygiene | yes |
| `feat/` | a new capability with proof obligations | yes, squash |
| `spike/` | throwaway exploration of a risky lemma; timeboxed | usually no — harvest and delete |
| `bench/` | benchmark programs and harness | yes |
| `exp/` | experiment runs, raw CSVs, plot scripts | yes (the data is a deliverable) |
| `fix/` | hardening, fuzzing, performance | yes |
| `docs/` | paper, README, TCB.md | yes |

**Rules.**

1. `main` is protected after M0. No direct pushes.
2. Squash-merge: one commit per feature on `main`, body listing the closed subtask IDs.
3. Every PR body states which subtasks close, which theorems changed status, and the `#print axioms` delta.
4. A branch lives ≤ 4 days. Longer means the feature was cut wrong — split it.
5. If a feature lands incomplete, the gap is a `sorry` **and** an entry in `docs/known-gaps.md`. `main` never carries an undocumented `sorry`.

---

## 3. Spikes — buy down the risk before spending on it

Three spikes run **before** the milestone that depends on them. Each is timeboxed, throws its code away, and answers a yes/no question. They are the cheapest insurance in the project, and G1a depends on one of them.

| Spike | Question | Timebox | When | If the answer is "no" |
|---|---|---|---|---|
| `spike/check-sound` | Is T5 really a one-page induction over a 20-line toy semantics? | 0.5 d | before M3 | Redesign the semantics before writing any domain |
| `spike/octagon-subst` | Can the substitution lemma for octagon transfer be stated and proved cleanly? | 1 d | post-month, before M7 | Keep octagons out permanently |
| `spike/reduce-idem` | Is a real reduction (interval into octagon) idempotent? | 0.5 d | post-month, before M8 | Keep the reduced product out permanently |

A spike branch is deleted after harvest. Its result is a paragraph in `docs/spikes.md` and a decision, not code.

---

## 4. Milestone map

| M | Name | Priority | ½d | Week | Branch(es) | Gate |
|---|---|---|---|---|---|---|
| M0 | Bootstrap | P0 | 3.0 | prep | `chore/bootstrap` | — |
| M1 | Semantics core | P0 | 4.0 | 1 | `feat/ast`, `feat/semantics` | — |
| M2 | Interval domain | P0 | 4.25 | 1 | `feat/domain-interval` | — |
| M3 | Checker + T5 | P0 | 5.5 | 1–2 | `feat/checker` | **G1a, G1b** |
| M4 | Certificate wire format | P0 | 3.0 | 2 | `feat/certificate-json` | — |
| M5 | Haskell driver | P0 | 4.5 | 2–3 | `feat/haskell-analyzer` | **G2** |
| M6 | Product combinator | P1 | 2.5 | 3 | `feat/domain-product` | — |
| M9 | Labels / path sensitivity | P1 | 4.0 | 3 | `feat/labels` | **G3** (with M10) |
| M10 | Benchmarks + experiment | P0 | 4.5 | 3–4 | `bench/suite`, `exp/frontier` | **G3** |
| M11 | Hardening | P0 | 2.75 | 4 | `fix/hardening` | — |
| M12 | Write-up + artifact | P0 | 3.0 | 4 | `docs/paper` | ship |
| M13 | Buffer | — | 2.0 | 4 | — | — |
| | **In-month total (main window)** | | **38.0 + 2.0 buffer = 40.0** | | | |
| M7 | Octagons | post-month | 4.0 | — | `feat/domain-octagon` | — |
| M8 | Reduced product | post-month | 4.5 | — | `feat/domain-reduced-product` | — |

**P0** = must ship · **P1** = should ship · **post-month** = designed, branched, not attempted in the 4 weeks.

### 4.1 Why octagons and the reduced product are post-month

The plan (`certcore-project-plan.md` §8.3) put octagons at L1, i.e. in-month. **The roadmap demotes them, and the reason is arithmetic, not taste.**

Adding M7 (4.0) and M8 (4.5) to the in-month scope gives 46.5 ½d against 40 available — a 6.5 ½d overrun, which is not absorbable by trimming. So something has to go, and the candidates are: octagons, labels, the reduced product, or the measurement.

- **The reduced product (M8)** is the easiest cut: it is one combinator, its claim (C2) survives on the product alone, and nothing else depends on it.
- **Labels (M9)** cannot go. They carry claim **C3** — the conceptual contribution — and they produce a far steeper precision-per-byte curve than relationality does, which is what the thesis (C4) needs to be visible at all.
- **Octagons (M7)** are the second-best cut. They demonstrate R5 (a third-party domain plugs in) — but so does M6's product instance. Their real job was the *domain axis* of the north-star plot, and depth provides that axis instead, more cheaply.

So the plot in the 4-week version is **safe-programs vs certificate bytes across label depth {0,1,2}**, with the octagon axis as the post-month extension. The thesis is intact; one axis is deferred.

This is a **deviation from the plan and should be recorded as such** — when the plan and the roadmap disagree, the roadmap wins on scheduling and the plan gets amended, not the other way round.

---

## 5. Schedule

```
day   1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
      │  │  │  │  │  │  │  │  │  │  │  │  │  │  │  │  │  │  │  │
M1    ████████
M2       ██████████
M3             ██████████████████
                    ▲ G1a (day 5, from spike)
                          ▲ G1b (day 7)
M4                      ██████
M5                         ██████████████
                                 ▲ G2 (day 10)
M6                              ██████
M9                                 ████████
M10                                    ████████████
                                             ▲ G3 (day 15)
M11                                             █████
M12                                             ██████
M13                                                   ████
      ════════════════════════════════════════════════════════════
      critical path: M1 → M2 → M3 → M4 → M5 → M9 → M10 → M12
      (indicative, not to scale)
```

**The critical path is the cheap spine**, and everything on it is P0 except M9 — which is exactly why M9 cannot be cut without weakening C3. Protect it; cut elsewhere.

Note the two gates around M3. **G1a** is the spike result: does T5 close on a toy semantics? It is cheap and it answers the project's central risk in week 1. **G1b** is the real thing, at day 7. Splitting them means a "no" arrives on day 5, not day 10.

---

## 6. Milestones

### M0 — Bootstrap (P0, 3.0 ½d, week 0 / prep)

**Goal.** A repo that builds, a CI that enforces the invariants we care about, and a frozen certificate schema before any code depends on it.

**Branch:** `chore/bootstrap`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M0.1 | Repo skeleton | `certcore/{lean,haskell,examples,bench,docs}`, MIT licence, `.gitignore` for `.lake/` and `dist-newstyle/` | 0.5 | — |
| M0.2 | Toolchain + Lake | Pin `lean-toolchain`, minimal `lakefile.toml`, **no Mathlib**; a `CertCore` library target plus a `certcore` executable | 0.5 | M0.1 |
| M0.3 | CI | GitHub Actions with a `.lake` cache; `lake build`; a grep step that fails the build on `sorry` inside `CertCore/` | 0.5 | M0.2 |
| M0.4 | Docs skeleton | README, `THEOREMS.md` with T1–T10 at status `todo`, `NONGOALS.md`, `TCB.md` stub, `known-gaps.md` | 0.5 | M0.1 |
| M0.5 | Freeze `docs/certificate-v1.md` | The JSON schema, field semantics, version string. **Changing this later costs a day** | 0.5 | — |
| M0.6 | Prior-art check for C1 | Search "certified abstract interpretation" + "verified certificate checker"; write `docs/prior-art.md`; reposition claims if the space is occupied | 0.5 | — |

**Exit:** CI green on an empty build; schema reviewed once, out loud, against the plan's §10.3; `THEOREMS.md` lists all ten theorems.

---

### M1 — Semantics core (P0, 4.0 ½d, week 1)

**Goal.** A language whose failure modes *are* the safety property, so that "safe" is defined by the semantics rather than by a separate document nobody checks.

**Branches:** `feat/ast` (M1.1–M1.3), `feat/semantics` (M1.4–M1.11)

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M1.1 | `I32` with wrap | Bounded 32-bit integers with explicit wrap-around. Overflow must be *observable*, not impossible by construction — it is the property under test | 0.25 | M0 |
| M1.2 | `Expr` | Constants, variables, binary ops, array read, array length | 0.25 | M1.1 |
| M1.3 | `Cmd` + `Program` | `skip`, assign, store, seq, if, while, assert, div; programs carry labelled points | 0.5 | M1.2 |
| M1.4 | `State` | `env : Var → I32`, `mem : Nat → Array I32` — total functions, so the semantics never gets stuck on a missing variable | 0.25 | M1.2 |
| M1.5 | `eval` | Expression evaluation to `Option I32`: `none` for division by zero, overflow, and out-of-bounds read. **This is where the safety property is defined** | 0.5 | M1.3, M1.4 |
| M1.6 | `step` | One-command transition; a failing `eval` and a failed `assert` both yield `none` | 0.75 | M1.5 |
| M1.7 | `run` + `Safe` | Fuel-indexed run; `Safe c s := ∀ n, run n c s ≠ none` — no coinduction anywhere | 0.25 | M1.6 |
| M1.8 | CFG `edges` | `Edge = Point × Cmd × Point`; the checker's obligations are indexed by these | 0.25 | M1.3 |
| M1.9 | **T1** `step_det` | Determinism, by induction on the command and on `eval` | 0.5 | M1.6 |
| M1.10 | **T2** `safe_iff` | `Safe` unfolds to the finite-prefix property; the escape hatch that keeps every later proof an ordinary induction | 0.25 | M1.7 |
| M1.11 | Three example programs | `.imp` files: one safe, one division-by-zero, one array overflow | 0.25 | M1.6 |

**Exit:** `lake build` green; T1 and T2 closed; the three examples evaluate to the expected `Option` values under `#eval`.

**Why this milestone is the riskiest cheap one.** If `Safe` needs coinduction or a termination side-condition, every later proof inherits the pain. M1.10 must close in week 1.

---

### M2 — Interval domain (P0, 4.25 ½d, week 1)

**Goal.** The first `CertDomain`, built exactly the way the kernel will demand every other domain be built: every operation carries its own soundness proof.

**Branch:** `feat/domain-interval`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M2.1 | `Interval` type | `lo`/`hi` with an explicit empty case; `toInterval : I32 → Interval` | 0.25 | M1 |
| M2.2 | `gamma` | `Interval → Set I32`, the concretisation. Every later lemma is phrased against this | 0.25 | M2.1 |
| M2.3 | `ble` + **T4a** `ble_sound` | Executable inclusion by comparing endpoints; the reflection lemma the checker needs | 0.5 | M2.2 |
| M2.4 | `join` + **T4b** `join_sound` | Convex hull, so the check has something to compare against | 0.5 | M2.2 |
| M2.5 | `top` + `top_sound` | The "no information" element | 0.25 | M2.2 |
| M2.6 | `transfer` (arithmetic) + **T4c** | Assign/const/binop; overflow either saturates or collapses to `top` — decide once, document it | 1.0 | M2.4 |
| M2.7 | `transfer` (arrays) | Read and length, plus the bounds predicate that becomes a safety obligation | 0.5 | M2.6 |
| M2.8 | `CertDomain` instance | Assemble the pieces. **This is where the kernel's generality first pays off** | 0.5 | M2.3–M2.7 |
| M2.9 | Interval unit tests | Ten `#eval` cases with hand-computed answers, checked in | 0.5 | M2.8 |

**Exit:** the instance typechecks with no `sorry`; ten unit tests pass; `#print axioms` on `ble_sound` is clean.

---

### M3 — Checker and T5 (P0, 5.5 ½d, week 1–2) · **Gates G1a, G1b**

**Goal.** The load-bearing theorem: a checker that performs no search, returns a typed diagnostic, and proves safety once for all domains.

**Branch:** `feat/checker`
**Spike:** `spike/check-sound` first (0.5 d, not counted in M3's estimate).

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M3.1 | `Certificate` type | Entry state, sparse point→state map, per-edge successor states, assertion states. Lean-side for now; JSON is M4 | 0.5 | M2 |
| M3.2 | `Diagnostic` | `(point, edge, obligation kind, expected, actual)` plus `Except` plumbing — the rejection is a *value*, not a string | 0.5 | M3.1 |
| M3.3 | `check` skeleton | Signature, lookup helpers, total failure behaviour; obligations filled in next | 0.5 | M3.2 |
| M3.4 | Init obligation | `γ(entry) ⊇ Init` | 0.25 | M3.3 |
| M3.5 | Edge obligation | `ble (transfer c (at p)) (at q)` for every edge — one `ble` call, no search | 0.5 | M3.3 |
| M3.6 | Safety obligation | `ble (at p) (safePred p)` at every assert and every partial operation | 0.5 | M3.3 |
| M3.7 | **T5** `check_sound` | The induction: any reachable state is in the invariant, hence never violates the predicate. **If this is not a page, stop and fix the semantics** | 2.0 | M3.4–M3.6, M1.9 |
| M3.8 | Axiom audit | `Audit.lean` with `#print axioms check_sound`; document the expected output | 0.25 | M3.7 |
| M3.9 | Golden accept test | One program, one hand-written certificate, `check` returns `.ok` | 0.5 | M3.7 |

**Exit (G1b, day 7):** `check_sound` closed with no `sorry`; axiom footprint is `{propext, Quot.sound}` or smaller; one end-to-end accept; one hand-corrupted certificate rejected with a sensible diagnostic.

**If T5 is not closed by day 7:** cut M9 (labels) and ship the intervals-only kernel. The project then has C1, C2, C4-weak and loses C3. That is a real loss — which is why G1a exists to give three days' warning.

---

### M4 — Certificate wire format (P0, 3.0 ½d, week 2)

**Goal.** A total decoder, so a hostile or malformed certificate is a *rejection*, not a crash.

**Branch:** `feat/certificate-json`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M4.1 | `encode` | Lean-side `Certificate → Json`; needed by tests even though the analyzer does the real emitting | 0.5 | M3.1 |
| M4.2 | `decode` (total) | Every field checked; malformed input returns `Diagnostic.malformed`. No partial functions anywhere on the path | 1.0 | M4.1 |
| M4.3 | **T10** `decode_sound` | A well-formedness predicate, and the theorem that successful decoding implies it | 0.5 | M4.2 |
| M4.4 | Round-trip property | `decode (encode c) = some c` on generated certificates | 0.5 | M4.2 |
| M4.5 | CLI `certcore check` | Read `.imp` + `cert.json`, print verdict or diagnostic; exit code 0/1/2 | 0.5 | M4.2 |

**Exit:** a 10-case malformed table all rejected cleanly; round-trip test green; CLI works on M3.9's golden pair.

---

### M5 — Haskell driver (P0, 4.5 ½d, week 2–3) · **Gate G2**

**Goal.** An analyzer that is deliberately untrusted, deliberately in another language, and good enough to produce certificates worth checking.

**Branch:** `feat/haskell-analyzer`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M5.1 | Haskell AST + parser | Reads the program JSON emitted by the Lean frontend. **Must agree with the Lean AST exactly** — a disagreement here is a bug the checker cannot catch | 0.5 | M4.5 |
| M5.2 | Transfer functions (mirrored) | Interval and array transfer re-implemented in Haskell. The duplication is the point: divergence shows up at the boundary | 1.0 | M5.1 |
| M5.3 | Chaotic iteration | Worklist fixpoint over the CFG | 1.0 | M5.2 |
| M5.4 | Widening | A simple threshold scheme; unsound widening is *acceptable* because the checker will reject | 0.5 | M5.3 |
| M5.5 | Certificate emitter | Sparse map + JSON, matching schema v1 | 0.5 | M5.3 |
| M5.6 | Repair loop | On `Diagnostic`, retry once with reduced precision or a dropped label | 0.5 | M5.5 |
| M5.7 | Differential test | Random states → compare Haskell and Lean transfer outputs; disagreements are bugs in one of them | 0.5 | M5.2 |

**Exit (G2, day 10):** ≥ 10 benchmark programs verified end-to-end (Haskell emits, Lean accepts); at least one certificate deliberately corrupted and rejected.

---

### M6 — Product combinator (P1, 2.5 ½d, week 3)

**Goal.** Prove in practice that a lift needs no new certificate theory — it is just a `CertDomain` instance.

**Branch:** `feat/domain-product`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M6.1 | Pair domain | `Abs := A × B`, componentwise everything | 0.5 | M2 |
| M6.2 | **T6** three soundness fields | `ble_sound`, `transfer_sound`, `join_sound` for the pair | 1.0 | M6.1 |
| M6.3 | Derived instance | The instance built *from* two `CertDomain` values, not from two concrete types — the genericity claim, made executable | 0.5 | M6.2 |
| M6.4 | Instance test | A program the pair proves and that neither component proves alone | 0.5 | M6.3 |

**Exit:** T6 closed; the isolated-precision test passes; **zero lines changed in `Check.lean`**.

M6.4 is the milestone's real result. "Zero lines changed in `Check.lean`" is the sentence that goes in the paper.

---

### M9 — Labels / path sensitivity (P1, 4.0 ½d, week 3)

**Goal.** The conceptual claim: path sensitivity is a product, not a new certificate theory. If this works, C3 is real.

**Branch:** `feat/labels`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M9.1 | `Flat(K)` domain | Finite label set; `ble` is equality; trivially decidable | 0.5 | M6 |
| M9.2 | Instrumented semantics | `step# : Cmd → State × Label → Option (State × Label)`; the label is updated deterministically by each step | 1.0 | M1 |
| M9.3 | **T9** `label_sim` | Projection: instrumented steps project to ordinary steps; errors preserved in both directions | 1.0 | M9.2 |
| M9.4 | `D × Flat(K)` instance | The label product, built from M6's combinator — no new code in the kernel | 0.5 | M9.1, M9.3 |
| M9.5 | Depth 0/1/2 in the driver | Label depth as a CLI flag; certificate size grows as expected | 0.5 | M9.4, M5.6 |
| M9.6 | The demo program | One `.imp` file where depth 0 proves nothing and depth 2 proves safety | 0.5 | M9.5 |

**Exit:** T9 closed; M9.6's program is the demo; certificate byte counts recorded for depths 0/1/2.

---

### M10 — Benchmarks and the experiment (P0, 4.5 ½d, week 3–4) · **Gate G3**

**Goal.** The north-star figure, and the number that backs C4.

**Branches:** `bench/suite` (M10.1), `exp/frontier` (M10.2–M10.5)

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M10.1 | Benchmark suite | ~30 programs in 5 families: straight-line, loops needing widening, array bounds, path-sensitive, small kernels | 1.5 | M1 |
| M10.2 | Harness | Runs analyzer → checker, records verdict, cert bytes, analyze/check times into CSV | 1.0 | M5, M10.1 |
| M10.3 | Mutation fuzzer | 10 000 mutated certificates; assert zero accepts, zero crashes | 1.0 | M4.2 |
| M10.4 | Plot script | The north-star figure: safe-programs vs cert bytes by label depth, with checker time overlaid | 0.5 | M10.2 |
| M10.5 | Failure analysis | Enumerate the programs no configuration certifies, one line of explanation each | 0.5 | M10.4 |

**Exit (G3, day 15):** the plot exists and is not embarrassing; raw CSV checked in; mutation fuzz reports 0/10 000.

**If the plot is embarrassing** — certificate size explodes before precision improves — that is a *finding*, not a failure. It goes in the paper as the measured cost of expressiveness. Do not tune the benchmarks to hide it.

---

### M11 — Hardening (P0, 2.75 ½d, week 4)

**Goal.** Make the artifact survive a stranger with a fuzzer.

**Branch:** `fix/hardening`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M11.1 | Fuzz triage | Every crash and every accepted mutation becomes a regression test | 0.5 | M10.3 |
| M11.2 | Adversarial decoder tests | Huge arrays, negative sizes, cyclic refs, duplicate points, wrong program hash | 1.0 | M4.2 |
| M11.3 | `ble` performance pass | `UInt64` backing, no allocation in the hot path; before/after numbers | 0.5 | M3.5 |
| M11.4 | Axiom audit in CI | Fail the build if `check_sound`'s axiom footprint changes | 0.25 | M3.8 |
| M11.5 | `TCB.md` finalised | One page: every trusted component, every trusted translation, and why | 0.5 | M4 |

**Exit:** zero accepted mutations; zero crashes on malformed input; CI enforces the axiom footprint; `TCB.md` complete.

---

### M12 — Write-up and artifact (P0, 3.0 ½d, week 4)

**Goal.** Something a stranger can reproduce in an afternoon.

**Branch:** `docs/paper`

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M12.1 | `THEOREMS.md` complete | All ten with statement, status, and the file where each is proved | 0.5 | M3–M9 |
| M12.2 | Paper draft | 8 pages: problem, design, T5/T6/T9, measurements, threats to validity | 1.5 | M10 |
| M12.3 | Demo script + recording | The 3-minute demo from the plan's §12.7, reproducible | 0.5 | M4.5 |
| M12.4 | README + reproduction | Clean-clone instructions that work on a machine that is not yours | 0.5 | M11 |

**Exit:** the DoD checklist in the plan's §14 fully ticked.

---

### M13 — Buffer (2.0 ½d, week 4)

Deliberately unallocated. It will be spent. Do not pre-assign it: the point of a buffer is to absorb the thing you did not predict, and every project has one.

---

## 7. Post-month backlog

Designed, branched, and deliberately not attempted. Each already has a spike gate in §3.

### M7 — Octagons (4.0 ½d)

**Branch:** `feat/domain-octagon`. Adds the relational *domain axis* to the plot (C4 strengthens) and demonstrates R5 on a genuinely non-trivial domain.

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M7.1 | DBM representation | Bounds on `±x ± y`, with the emptiness convention | 0.5 | M2 |
| M7.2 | Closure | Floyd–Warshall over the DBM, plus `closure_sound`: every implied constraint is genuinely implied | 1.0 | M7.1 |
| M7.3 | `ble` via closure | Inclusion by closure + endpoint comparison, plus `ble_sound` | 0.5 | M7.2 |
| M7.4 | Transfer + `transfer_sound` | Substitution into a DBM for assignment and guards. **The hard part** | 1.5 | M7.2 |
| M7.5 | `CertDomain` instance | Wrap it up; no changes to the kernel | 0.5 | M7.3, M7.4 |

### M8 — Reduced product (4.5 ½d)

**Branch:** `feat/domain-reduced-product`. The interesting combinator: precision neither component has, with the reduction *recorded* so the checker can replay it.

| ID | Subtask | What it does | ½d | Dep |
|---|---|---|---|---|
| M8.1 | Reduction interface | `ρ : A × B → A × B` plus the hint type recording which reductions fired | 0.5 | M6 |
| M8.2 | **T7a** soundness | `γ(ρ(a,b)) ⊆ γ(a) ∩ γ(b)` | 1.5 | M8.1 |
| M8.3 | **T7b** idempotence | `ρ ∘ ρ = ρ` — without this the post-fixpoint check never closes on the analyzer's real output | 1.0 | M8.2 |
| M8.4 | Hint replay | Checker-side `verify`: replay the recorded reductions, confirm they produce the claimed state | 1.0 | M8.3 |
| M8.5 | Instance + tests | Interval × octagon with a real reduction; before/after precision | 0.5 | M8.4 |

---

## 8. Dependency graph

```
M0 ─▶ M1 ─▶ M2 ─▶ M3 ─┬─▶ M4 ─▶ M5 ─┬─▶ M6 ─▶ M9 ─▶ M10 ─▶ M11 ─▶ M12
                      │              │
                      │              └─▶ M7 ─▶ M8      (post-month)
                      │
                      └─▶ (M3.8 feeds M11.4)
```

Only two things are strictly sequential: **M1→M2→M3** (the spine) and **M4→M5** (the protocol). M6 and M9 sit on the critical path only because the thesis needs them; M7 and M8 hang off the side and can be done in any order, or never.

---

## 9. Budget vs capacity

| Window | Available | Planned | Delta | Composition |
|---|---|---|---|---|
| Prep (2 days) | 4.0 | 3.0 | +1.0 | M0 |
| Week 1 | 10.0 | 11.0 | −1.0 | M1 4.0 + M2 4.25 + M3.1–3.6 2.75 |
| Week 2 | 10.0 | 8.75 | +1.25 | M3.7–3.9 2.75 + M4 3.0 + M5.1–5.4 3.0 |
| Week 3 | 10.0 | 10.5 | −0.5 | M5.5–5.7 1.5 + M6 2.5 + M9 4.0 + M10.1 1.5 + M10.2 1.0 |
| Week 4 | 10.0 | 9.75 | +0.25 | M10.3–10.5 2.0 + M11 2.75 + M12 3.0 + buffer 2.0 |
| **Main total** | **40.0** | **40.0** | **0.0** | **38.0 named + 2.0 buffer** |

Week 1 is over by a half-day and week 2 is over by a quarter. That is deliberate: the front of the schedule is where uncertainty is highest, and the fix is cheap — **M3.1–M3.3 (the checker's scaffolding, 1.5) can slide into week 2 without touching G1a**, which comes from the spike, not from the scaffolding. Weeks 3–4 then absorb the rest, with the buffer covering the 0.5 overrun in week 3.

**The budget closes exactly at 40.** That is the whole reason §4.1 moves two milestones out. A roadmap that claims everything fits is a roadmap that has not added up its own numbers.

---

## 10. Release valves — what to cut, in order

When a gate slips, cut from this list, top first. Do not improvise.

| # | Cut | Saves | Consequence |
|---|---|---|---|
| 1 | **M10.1** to 15 programs | 0.5 | Thinner evidence; state the sample size honestly |
| 2 | **M5.6** repair loop | 0.5 | Demo loses the "analyzer iterates" story; checker unaffected |
| 3 | **M9.5** depth 2 | 0.5 | Curve is depth {0,1}; flatter, still real |
| 4 | **M11.3** perf pass | 0.5 | Report unoptimised times with a caveat |
| 5 | **M6.4** isolated-precision test | 0.5 | Weaker illustration of the product's value |
| 6 | **M12.2** to 4 pages | 1.0 | A workshop abstract instead of a paper |
| 7 | **M9** (labels) — the last resort | 4.0 | **C3 is gone.** The project becomes "a verified interval checker", which is a real but much smaller thing |

**Never cut:** M1.10 (T2), M3.7 (T5), M4.2 (total decoder), M10.3 (mutation fuzz), M11.4 (axiom audit). Those five *are* the claim. Cutting any of them turns the project into a demo.

---

## 11. Commit and PR conventions

**Commit:** `M3.7: prove check_sound for the interval instance`

```
<subtask-id>: <imperative summary>

<one or two sentences on what changed and why>

Theorem status: T5 todo -> proved
Axioms: unchanged
```

**PR title:** `feat/checker: M3 — checker and T5`

**PR body:** closed subtasks, theorem status diff, axiom delta, and one sentence on what a reviewer should look at first. Keep it to a screen.

---

## 12. The four dates that matter

1. **Day 5 — G1a.** Does T5 close on a toy semantics? A "no" here is worth more than a week of optimism.
2. **Day 7 — G1b.** Is `check_sound` closed on the real interval semantics? If yes, the project exists.
3. **Day 10 — G2.** Does a Haskell program's certificate get accepted by a Lean checker it has never talked to? If yes, C1 and C2 are real.
4. **Day 15 — G3.** Does the plot exist? If yes, C4 is real and week 4 is writing. If no, the paper becomes a design paper and the measurement moves post-month.

Everything else in this document is scheduling. Those four are the project.
