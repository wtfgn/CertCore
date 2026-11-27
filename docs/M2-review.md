# CertCore — Interim Review at M2

| | |
|---|---|
| Reviewed | 2026-11-26 |
| Milestone | **M2 — Interval domain** |
| Branch / commit | `feat/domain-interval` @ `a594435` (`M2.9: ten hand-computed interval cases`) |
| Build | `lake build` green, 29 jobs, no warnings |
| Tests | 19/19 green: `I32`, `Syntax`, `State`, `Eval`, `Step`, `Run`, `Edges`, `Compile`, `Examples`, `Interval`, `Gamma`, `Ble`, `BleSound`, `Join`, `Top`, `Transfer`, `Arrays`, `Instance`, `IntervalUnit` |
| `sorry` | none in `lean/` |
| Axioms (M1 sample) | `[propext, Quot.sound]` for the seven lemmas printed by `Audit.lean` |
| Axioms (M2) | **15 of the 43 proved M2 lemmas depend on `Classical.choice`**, including `join_sound`, `assign_sound`, `evalExpr_sound`, and the instance's `transferAbs_sound`. `ble_sound` — the one lemma the milestone's exit criterion names — is clean. |
| Merge state | 9 commits ahead of `main` (`13f85ec`, M1); not merged |
| Verdict | **M2 is sound and code-complete, but not demo-complete or audit-clean.** The interval domain is real and its soundness fields typecheck, but the `CertDomain` interface is still missing the operations the checker needs (`entails`, `init`, `bot`, `P`-preservation), two showcase programs cannot yet be certified, and the audit gate does not cover the new trusted code. Fix the two `Classical.choice` roots and the docs before merge; settle the interface and the two precision gaps at the top of M3. |

This review is based on reading every Lean source, test, and design document;
building the tree; running all nineteen test files; grepping for `sorry`;
printing `#print axioms` for all 43 proved M2 lemmas; and reproducing two
transfer failures with `#eval` (reproduction in §11). No source file was changed
while writing this review.

---

## 0. Executive summary

- **The interval domain exists and is sound.** `Interval` (`bot` plus optional
  bounds with a validity proof), `gamma`, `ble`/T4a, `join`/T4b, `top`,
  `evalExpr`/`assign`/T4c, array read/len and `idxWithin`, and the assembled
  `intervalDomain` all typecheck. No soundness bug was found in the domain: every
  operation over-approximates, and every field of `CertDomain` has a proof.
- **The proof content is short and readable.** T4a/T4b/T4c are a few dozen lines
  each; `ble_sound` is about a dozen lines of case analysis. That is the intended shape:
  the checker's cost model is one `ble` per obligation, and the domain's proofs
  are small enough to audit.
- **The milestone's exit criteria are too weak.** They ask for "the instance
  typechecks, ten unit tests pass, and `#print axioms` on `ble_sound` is clean."
  All three hold. But `ble_sound` is one of the 28 M2 lemmas that *are* clean;
  `transferAbs_sound` (the instance's field) and `join_sound` are not. And no
  exit criterion asks the question that matters for M3: *can this domain certify
  the programs the project promises to demo?* It cannot, for either showcase
  (§7 F3).
- **The `CertDomain` interface is not yet the interface T5 needs.** The checker
  has three obligation families. The edge family is covered (modulo a `P s'`
  premise). The init family has no `init : Abs`; the safety family has no
  `entails`; the v1 `bot` state has no `bot` field or generic representation;
  and `P` is assumed preserved rather than proved preserved. This is the single
  most important handoff issue (§7 F1). `certificate-v1.md` §12.6 already asked
  for `entails` "before M2.6"; M2.6 passed without it.
- **The audit is an M1 audit.** `Audit.lean` imports `Semantics` only. It prints
  seven M1 lemmas and none of the new trusted code. Fifteen M2 lemmas carry
  `Classical.choice`, which the project's own policy calls a soundness hole (it
  is not — it is a consistent classical axiom — but it does violate the stated
  audit contract and would fail the planned M11.4 gate). The footprint has two
  small roots, and both are cheap to remove (§7 F2).
- **The tree grew a lot.** M2 adds ~1,900 lines across 20 files, of which about
  1,100 are trusted Lean. `TCB.md` still says "this is the M1 status" and does
  not list the interval modules; `known-gaps.md` still says "none — the M1 tree
  has no `sorry`". The documentation did not grow with the TCB (§7 F7).

**Bottom line.** M2 is a good milestone with a real domain, a clean proof shape,
and no soundness bug. It is not yet a usable kernel: the interface is
under-specified, two showcase programs are rejected for precision reasons, and
the audit has not been extended. The first two are design work for M3; the audit
is two one-line proof fixes and a script change. Do the cheap fixes before
merging, and put the interface decision first in M3.

---

## 1. In plain language

This section is for a reader who has never seen abstract interpretation or a
proof assistant. The technical review starts at §2.

### 1.1 The problem

A program can go wrong in four ways in this language: divide by zero, read or
write an array out of bounds, overflow a 32-bit integer, or fail an `assert`.
Running the program on a few inputs only tests those inputs. The project wants a
guarantee for **every** input.

The usual approach is to write a clever analyzer that searches for an argument
that the program is safe. Clever analyzers are big, and a bug in one produces a
wrong "safe" verdict. CertCore takes a different route.

### 1.2 Guess, then check: the referee idea

Split the work in two:

- an **analyzer** (later, in Haskell) *guesses* a proof;
- a tiny **checker** (in Lean) *verifies* the guess.

The guess is a **certificate**: a table that says, at each line of the program,
what is known about the variables. The checker does not search, does not
iterate, and does not trust the analyzer. It performs a fixed number of
arithmetic comparisons. If the table passes, the program is safe; if the table
is wrong, the checker rejects it.

The analogy is a maths exam with a small, strict marker. The student's working
can be wild or brilliant — the marker does not care. It checks the final line
against the rules. A wrong final line cannot pass, even if the working is
plausible. CertCore's "marker" is small enough that its own correctness can be
proved, mechanically, once.

The whole design is one sentence: **move every source of cleverness outside the
trusted base, and make the certificate the only interface.**

### 1.3 Boxes: what an interval is

An **interval** is a box around the possible values of a variable.
`x ∈ [0, 3]` means: for all we know, `x` is one of 0, 1, 2, 3. The box does not
say which; it is an *over-approximation*. Four special boxes:

| Box | Meaning |
|---|---|
| `[0, 3]` | a finite range |
| `(−∞, 5]` | unbounded below, bounded above |
| `top` = `(−∞, +∞)` | no information at all |
| `bot` = `∅` | no possible value: this line is unreachable |

The five operations in `Interval.lean` are the whole vocabulary:

| Operation | Plain meaning | Example |
|---|---|---|
| `gamma i v` | "the concrete value `v` fits in box `i`" | `gamma [0,3] 2` is true; `gamma [0,3] 4` is false |
| `ble a b` | "is box `a` inside box `b`?" | `ble [2,8] [0,10]` is true; the reverse is false |
| `join a b` | "the smallest box containing both" | `join [0,1] [3,4] = [0,4]` |
| `add`, `sub` | "the box of the result of `+`/`−`" | `[1,2] + [3,4] = [4,6]`; `[1,2] − [3,4] = [−3,−1]` |
| `top`, `bot` | "anything", "nothing" | every box is inside `top`; `bot` is inside every box |

`join` is where precision is lost: the smallest box containing `[0,1]` and
`[3,4]` is `[0,4]`, which also contains 2, a value neither branch can produce.

### 1.4 The three checks

The checker will verify three families of obligations. Each is one comparison.

1. **Start.** The box at the entry point must contain the initial state (all
   variables zero, arrays zero-filled).
2. **Step.** For every edge `p → q` in the control-flow graph, take the box at
   `p`, apply the instruction, and require the resulting box to be inside the
   box claimed at `q`. (This is the `transfer` + `ble` pair.)
3. **Safety.** At every risky instruction, the box must *guarantee* safety:
   the divisor's box must exclude 0; the index's box must be inside `[0, len)`;
   an `assert b` must be implied by the box.

There is no search in any of these. That is why checking time is linear and
predictable, and why a hostile certificate cannot make the checker run for
hours.

### 1.5 A tiny end-to-end example

Program (points on the left):

```text
0: x := 0
1: x := x + 1
2: assert (x == 1)
```

A certificate table:

```text
point 0: x ∈ [0, 0]      (before/at the first instruction)
point 1: x ∈ [0, 0]
point 2: x ∈ [1, 1]
```

The checks:

- **Start:** the initial state has `x = 0`, which is in the entry box `[0,0]`. ✓
- **Step 0 → 1:** applying `x := 0` to the entry box gives `[0,0]`; the table
  claims `[0,0]` at point 1, and `[0,0] ⊆ [0,0]`. ✓
- **Step 1 → 2:** applying `x := x + 1` to `[0,0]` gives `[1,1]`; the table
  claims `[1,1]` at point 2. ✓
- **Safety at 2:** `[1,1]` implies `x == 1`, so the assert cannot fail. ✓

Accept: the program is safe. This is the simplest possible certificate, and M2's
add transfer already handles it. The missing M3 pieces for this example are the
safety test (`entails`) and the init base (`init`).

### 1.6 The loop example, and why it is hard

`examples/safe.imp`:

```text
x := 0;
y := 1;
while (x < 3) { x := x + 1; }
assert (x == 3);
```

The analyzer might guess: at the loop head, `x ∈ [0,3]`. Is that guess
self-consistent? Check the body:

- On the true edge of `x < 3`, the body runs. **If the checker does not use the
  guard**, the body starts with the head box `[0,3]`.
- After `x := x + 1`, the box is `[1,4]`.
- The back edge returns to the head, whose claimed box is `[0,3]`.
- Is `[1,4]` inside `[0,3]`? **No.** The guess is rejected.

But the program is obviously safe. What is missing is the **guard fact**: on the
true edge, `x < 3`, so the body's box can be sharpened from `[0,3]` to `[0,2]`.
Then after `x + 1` the box is `[1,3]`, which is inside `[0,3]`; the guess is
inductive. On the false edge, `x ≥ 3` and the head box says `x ≤ 3`, so the exit
box is `[3,3]`, which proves `x == 3`.

That sharpening is called **guard refinement**, and M2 deliberately does not do
it: `transferAbs` maps every `assume` edge to the identity. This is sound (it
never claims more than it knows) but too weak to certify the project's own loop
example. It is the main precision gap found in this review (§7 F3).

### 1.7 The division example, and the current gap

`docs/certificate-v1.md` §13 is the canonical accepted certificate:

```text
0: x := 0
1: x := x + 1
2: y := 10 / x     -- safety: x ≠ 0
3: assert (y == 10)
```

At point 2, the box for `x` is `[1,1]`, so `x ≠ 0` is provable. The next step
assigns `y := 10 / x`. With `x ∈ [1,1]`, the result should be `y ∈ [10,10]`.
But M2's `evalExpr` maps every multiplication **and division** to `top`:

```lean
| .mul _ _ => top
| .div _ _ => top
```

So after point 2, `y` is `top`, and the table's claim `y ∈ [10,10]` at point 3 is
not satisfied: `top` is not inside `[10,10]`, so the edge obligation
`ble (transfer …) (state at 3)` is **false**. The agreed worked example cannot
be certified by the M2 domain. This is a precision gap, not a soundness bug: the
checker is conservative and rejects a program it cannot prove. It is, however,
the example the demo uses, so it is on the critical path (§7 F3).

Applying interval division is not hard for a singleton divisor like `[1,1]` or a
constant; full division (sign cases, truncation, zero) is more work. A
singleton/constant rule is enough for the worked example and is the recommended
first step.

### 1.8 Why labels exist

Consider:

```text
if (x == 0) { y := 1 } else { y := 2 }
assert (y == 1 || y == 2)
```

At the join, the interval domain has the box `y ∈ [1,2]`. That box also contains
1.5, which the program can never produce. A checker that only knows
`y ∈ [1,2]` cannot prove `y == 1 || y == 2`, because it cannot rule out 1.5.
The property is true, but the box is too coarse.

The fix is not a smarter `join`; it is to keep **two boxes**, one per branch
history, and never join them. That is path sensitivity, and the project's
conceptual claim (C3) is that it can be obtained as the product of the interval
domain with a finite **label** domain — no new certificate theory, just more
entries in the table. The cost is certificate size; the experiment (C4) measures
that cost. M2 stops before labels (M9), but the interval `join` is the operation
whose precision loss motivates them.

### 1.9 What is trusted

| Trusted | Untrusted |
|---|---|
| Lean's kernel and toolchain | the Haskell analyzer (future) |
| `I32` and the semantics | the Python benchmark harness (future) |
| the compiler and CFG | the certificate bytes themselves |
| the interval domain (`Interval.lean`, `IntervalTransfer.lean`, `IntervalArrays.lean`, `IntervalInstance.lean`) | — |
| the future decoder and checker | — |

The analyzer can be buggy, heuristic, or malicious. A bad guess produces a
certificate the checker rejects, never a wrong "safe". That is the point of the
architecture, and it is why the trusted side must be small and audited.

### 1.10 Why certificate size is a research question

More precision means more boxes: a box per program point, per branch history,
per label. The certificate grows, but checking stays linear because each box
comparison is cheap. The project's empirical claim is a measured curve — *how
many programs can you prove safe as you spend certificate bytes?* — with the
checker's trusted base fixed. M2 is the first domain on that curve. It cannot
yet certify its own showcase programs, which is why the next two milestones
(interface, then precision) matter more than adding another domain.

---

## 2. M2 against its contract

Roadmap M2 (`docs/certcore-roadmap.md` §6) asks for nine subtasks. Their state:

| ID | Subtask | Status | Evidence / deviation |
|---|---|---|---|
| M2.1 | `Interval` type | **done** | `bot` + `itv (Option I32) (Option I32) (loLeHi proof)`; `toInterval`; `ofBounds?` checked, `ofBounds` normalising. The validity proof makes inverted intervals unrepresentable. |
| M2.2 | `gamma` | **done** | `gamma : Interval → I32 → Prop`; `lowerOk`/`upperOk`; membership lemmas. A predicate, not a `Set`, because the tree is Mathlib-free. |
| M2.3 | `ble` + T4a | **done** | Endpoint comparison; `ble_sound` proved; `leLo`/`leHi` and their soundness lemmas. |
| M2.4 | `join` + T4b | **done** | Convex hull; `join_sound` proved; `loLeHi_min_max` establishes validity. |
| M2.5 | `top` + `top_sound` | **done** | `top = itv none none`; every value is in it. |
| M2.6 | arithmetic transfer + T4c | **done with a deviation** | `add`/`sub` exact; `mul`/`div` collapse to `top`; `evalExpr_sound` and `assign_sound` proved for the conservative transfer. The roadmap says "binop"; only `+`/`-` are precise. |
| M2.7 | array transfer | **done** | `Abs` with `mem`; `evalExprAbs`; `lenInterval`; `idxWithin`/`idxWithin_sound`; T4c for read/len. Store is M2.8. |
| M2.8 | `CertDomain` instance | **done, but the interface is incomplete** | The instance typechecks with all soundness fields (`bleAbs_sound`, `topAbs_sound`, `joinAbs_sound`, `transferAbs_sound`). But `CertDomain` has no `entails`, `init`, `bot`, or `P_step` (§7 F1), so it is not yet the structure T5 needs. |
| M2.9 | ten interval unit tests | **done** | `Tests/IntervalUnit.lean`: ten hand-computed cases, every one a `#guard`. |

**Exit criteria:** the instance typechecks with no `sorry` (yes); ten unit tests
pass (yes); `#print axioms` on `ble_sound` is clean (yes). All three are
satisfied. The criteria are nevertheless too weak for the same reason M1's were:
they sample one theorem and one class of test, and the sample is biased.

- The axiom criterion names `ble_sound`, which is clean; the assembled
  `transferAbs_sound` (the field T5 actually consumes) carries `Classical.choice`.
- The unit tests pin values of individual operations; none exercises the
  instance's `assume` transfer or asks whether a showcase program can be
  certified. Both fail (§7 F3).

**Verdict against the contract:** M2 is code-complete by its own checklist, and
the domain is sound, but the milestone boundary is the wrong place to stop for
the interface. The next commit should fix the audit and record the interface
decision before M3 begins.

---

## 3. The tree at a glance

*Line counts are at review time; `Get-Content` counts may differ from the
editor by a trailing newline.*

| File | Lines | Trust | Role | M2 state |
|---|---:|---|---|---|
| `lean/CertCore/I32.lean` | 270 | **yes** | signed 32-bit values; checked and wrapping arithmetic | inherited from M1, complete |
| `lean/CertCore/Semantics.lean` | 1,334 | **yes** | AST, state, `eval`, compiler, `step`/`run`/`Safe`, `edges`, `WF`, T1/T2, `step_edge` | inherited from M1, complete |
| `lean/CertCore/Domain.lean` | 58 | **yes** | the `CertDomain` structure: the kernel's plug-in socket | M2.8 interface; **missing four operations** (§7 F1) |
| `lean/CertCore/Domain/Interval.lean` | 389 | **yes** | interval value, `gamma`, `ble`/T4a, `join`/T4b, `top` | complete |
| `lean/CertCore/Domain/IntervalTransfer.lean` | 292 | **yes** | `Env`, interval `add`/`sub`, `evalExpr`, `assign`, T4c | complete for the conservative transfer; `mul`/`div` are `top` |
| `lean/CertCore/Domain/IntervalArrays.lean` | 149 | **yes** | `Abs` with `mem`, `AbsSound`, `evalExprAbs`, `lenInterval`, `idxWithin` | complete; the `AbsSound` family is used only by tests |
| `lean/CertCore/Domain/IntervalInstance.lean` | 298 | **yes** | `GammaOn`, `POn`, support-restricted evaluator, `store`, `bleAbs`, `joinAbs`, `transferAbs`, `intervalDomain` | the assembled instance |
| `lean/CertCore/Cert.lean` | 21 | yes | certificate type + total decoder | **stub** (M4) |
| `lean/CertCore/Check.lean` | 20 | yes | three obligation families + diagnostic | **stub** (M3) |
| `lean/CertCore/Proofs.lean` | 14 | yes | theorem aggregator | **stub** |
| `lean/CertCore/Audit.lean` | 29 | yes | `#print axioms` gate | **M1 only**; does not import the interval modules |
| `lean/CertCore/Cli.lean` | 19 | yes | `certcore` executable | **stub**; still says "M1 semantics core" |
| `lean/Tests/*.lean` | ~1,372 | no | executable boundary tests | 19 files, 256 `#guard`s |
| `docs/*.md` | — | — | plan, roadmap, theorems, TCB, format, gaps | partly stale after M2 (§7 F7) |

The M2 branch is nine commits ahead of `main` (`13f85ec`, M1), one commit per
subtask, on the branch named by the roadmap. That is good process: the branch is
the feature, the commits are the subtasks, and each commit leaves the tree green.
The branch is not merged, so CI on `main` has not exercised M2 (§7 F7).

Two consequences of the table:

1. **The trusted tree grew by about 1,100 lines.** `TCB.md` still describes the
   M1 boundary. The interval domain is now a trusted component; a bug in
   `Interval.ble` or `transferAbs` changes a verdict, exactly like a bug in
   `Semantics`. The TCB document must list it.
2. **Two of the three transfer towers are not on the final path.** The instance
   uses `evalExprAbsOn`/`assignAbsOn`; `IntervalTransfer`'s `Env` evaluator and
   `IntervalArrays`'s `AbsSound` evaluator are used by tests and by the lower
   layer, not by the assembled instance. This is a TCB-surface issue (§7 F6).

---

## 4. What each part does, and why it matters to the whole

### 4.1 `I32` — the arithmetic substrate (inherited)

`I32` is an `Int` with a range proof. Checked operations (`add?`, `sub?`,
`mul?`, `div?`) return `none` exactly when the mathematical result leaves
`[-2^31, 2^31−1]`; wrap operations model the machine; `ofIntWrap_agrees` proves
they agree when the checked operation succeeds.

**Contribution.** The safety property is about 32-bit failure. If overflow were
impossible by construction, or silent, the project would certify a different
property. The checked/wrap split lets the semantics treat overflow as a failure
while still having a machine model. `Interval`'s endpoint arithmetic uses the
checked operations: an endpoint sum that overflows collapses the interval to
`top` (§4.5), which is sound because `top` contains every value.

**Cost/risk.** `I32` is inherited and was reviewed at M1. The one standing
footgun is that `OfNat I32` wraps, so a specification numeral beyond range
silently wraps; the tests use `I32.ofIntWrap` deliberately, and trusted code uses
`ofInt?`. No new risk at M2.

### 4.2 `Semantics` — the language and the machine (inherited)

The structured AST (`Expr`, `BExp`, `Cmd`, `Program`), the total state, the
edge-machine compiler (`Cmd.compile`/`Program.compile`), the deterministic
`step`, the fuel-indexed `run`, `Safe` as the finite-prefix property, the
checker-facing `edges`, the well-formedness theorem `compile_wf`, and the bridge
`step_edge` (every successful step is one edge of the graph).

**Contribution.** This is the object the domain is *about*. The interval domain
never inspects a `Cmd` directly; it transfers over `EdgeCmd`, the checker's edge
label. `step_edge` is what will let T5 turn an edge obligation into a fact about
the actual transition. `Program.safe` includes `Program.WF`, so a malformed
program is never certified.

**Cost/risk.** The compiler is trusted and has no independent source semantics;
M1's F1 was a compiler bug, and the post-review fix (`maxPoint` recursion,
`compile_wf`) was the right containment. M2 inherits a clean base.

### 4.3 `Domain.lean` — the kernel's socket

`CertDomain` is the structure the whole project is parameterised by:

```lean
structure CertDomain where
  P : State → Prop
  Abs : Type
  gamma : Abs → State → Prop
  ble : Abs → Abs → Bool
  ble_sound : ...
  top : Abs
  top_sound : ...
  transfer : EdgeCmd → Abs → Abs
  transfer_sound : ...
  join : Abs → Abs → Abs
  join_sound : ...
```

**Contribution.** This is the extension point that makes C1/R5 possible: a third
party supplies an `Abs`, a `gamma`, an executable `ble`, and proofs; the generic
checker and the one soundness theorem do the rest. The `P` parameter is the
program-state invariant (fixed array lengths): `top_sound` can only claim `s ∈ γ
top` for states satisfying `P`, because an interval cannot describe an array's
length. `transfer` is over `EdgeCmd` — the checker-facing edge action — not the
source `Cmd`, which is M1's F5 resolution.

**Cost/risk.** The socket has eleven fields; the checker needs several more. The
missing ones are the subject of F1: `init`/`init_sound` (base case),
`entails`/`entails_sound` (safety obligations), `bot`/`bot_sound` (v1's explicit
unreachable state), and a `P_step` preservation obligation (the induction
invariant). The structure is the right *shape*; it is not yet complete. This is
the most important finding in the review, because it is cheapest to fix now.

### 4.4 `Domain/Interval.lean` — the box

The value type and the five core operations: `bot`/`itv`, `gamma`, `ble`/T4a,
`join`/T4b, `top`. The `valid : loLeHi lo hi` proof is a small design win: an
inverted interval is not representable, so `bot` is the *only* empty interval,
and every pattern match is total.

**Contribution.** This is the first concrete domain, and the template every
other domain follows. The operations are the entire vocabulary the checker will
use: `ble` is the edge obligation, `gamma` is the meaning, `join` is what the
analyzer uses to merge, `top` is the default for missing certificate states.

**Cost/risk.** `join` is the convex hull, so it loses the gap information that
labels later recover. `toInterval`'s validity proof is currently written with
`simp`, which is the root of the `Classical.choice` footprint (F2); a one-line
constructive proof fixes it. The type's `DecidableEq` deriving is fine for tests;
the trusted proofs do not depend on it.

### 4.5 `Domain/IntervalTransfer.lean` — the arithmetic engine

`Env`, checked endpoint arithmetic, `add`/`sub`, `evalExpr`, `assign`, and T4c
(`evalExpr_sound`, `assign_sound`). Addition and subtraction are exact over the
abstract bounds; if a finite endpoint overflows, the result is `top`, not a wrap.

**Contribution.** This is where a concrete instruction becomes an abstract box.
`evalExpr` is the recursion the instance reuses (`evalExprAbsOn` calls `add` and
`sub` directly); `evalExpr_sound` is the T4c field for expressions. The overflow
policy is one line to state and one line to prove, which is the point.

**Cost/risk.** `mul` and `div` are `top`; array read and `len` are `top` in this
layer (they become precise at M2.7). The computed `Env` evaluator is not used by
the assembled instance, which uses the support-restricted evaluator instead
(F6). The canonical worked example needs division, so this layer's conservative
choice is the direct cause of F3.

### 4.6 `Domain/IntervalArrays.lean` — arrays as summaries

`Abs` has two components: `vars : Var → Interval` and `mem : Arr → Interval`,
one interval covering **every cell** of each array. `AbsSound` requires every
in-bounds cell to be in the array's interval; `evalExprAbs` returns the array
interval for a read and the declared length for `len`; `idxWithin` is the bounds
predicate and `idxWithin_sound` proves it implies `0 ≤ i < len`.

**Contribution.** Array bounds are one of the four safety properties, and a
single summary per array is enough to prove them: the index's box and the
declared length are all `idxWithin` needs. This keeps the abstract state small
and the certificate's per-point state finite.

**Cost/risk.** `store` (at M2.8) sets the written array to `top`, so contents are
lost; the `AbsSound` family is used only by `Tests/Arrays.lean`, not by the
instance (F6). More importantly, the `mem` component **cannot be encoded in v1**
— the frozen format's state is `vars` only (§7 F5). The end-to-end checker will
have to set `mem` to `top`, so M2.7's precise read transfer is currently
unreachable from a v1 certificate. Decide before M4.1.

### 4.7 `Domain/IntervalInstance.lean` — the assembled domain

`GammaOn` (concretisation over a finite support of variables and arrays),
`POn` (every array has its declared length), the support-restricted evaluator,
`storeAbsOn` (written array → `top`), `topAbs`, `bleAbs`/`joinAbs`, `transferAbs`
(the `EdgeCmd` transfer), and `intervalDomain`, the `CertDomain` record that
bundles them with their soundness proofs.

**Contribution.** This is M2's headline: the first complete `CertDomain`
instance, the thing T5 will be instantiated at. The support restriction is a
sound way to handle names outside the program's finite support: an unknown
variable or array evaluates to `top`, so the instance never needs the abstract
state to be defined for every string or array.

**Cost/risk.** The instance is sound but under-powered for the demos: `assume`
is the identity (no guard refinement), `store` is `top`, and `mul`/`div` are
`top`. The `P s'` premise in `transfer_sound` is assumed, not derived; T5 needs
a preservation lemma (F1). The support restriction also produces a second
transfer tower (`*On`) alongside the unrestricted one (F6).

### 4.8 The stubs (`Cert`, `Check`, `Proofs`, `Audit`, `Cli`)

`Cert.lean`, `Check.lean`, and `Proofs.lean` are design documents in Lean
syntax: they state the intended interfaces and obligations, with no definitions.
`Audit.lean` is a real script but imports `Semantics` only. `Cli.lean` prints a
version string and still says "M1 semantics core".

**Contribution.** The stubs are honest signposts: they say exactly what M3/M4
will build. `Check.lean`'s comment already names the three obligation families;
`Cert.lean` names the total decoder; `Audit.lean` shows the intended gate.

**Cost/risk.** `Audit.lean` is the only one that is load-bearing, and it is
stale: it does not import the interval modules, so the M2 trusted code is
outside the gate. `Cli.lean` and the README quick start still print the M1
message. These are cheap documentation/CI fixes (F7).

### 4.9 Tests — the executable boundary

Nineteen files, 256 `#guard`s, no test framework. A `#guard` is a compile-time
assertion: a false expectation fails elaboration, so it fails the build. The
tests cover the I32 boundary, syntax/entry, state updates, the four hazards,
compilation/WF, the example outcomes, and every M2 operation.

**Contribution.** The trusted definitions are not *proved* correct by these
tests, but they are pinned against drift. The `#guard` style is the right
low-dependency choice for a Mathlib-free tree: one command per file, no test
runner, and CI runs each file.

**Cost/risk.** The tests are value-biased. They pin what each operation returns
on chosen boxes; they do not test the *interface*: no `assume` transfer test, no
`POn`-at-`init` test, no end-to-end certificate (the checker does not exist yet),
and no negative test for `ble` completeness. That is exactly how the two
showcase gaps survived (§7 F3, F8).

### 4.10 Documents — the contract

`THEOREMS.md` (the T1–T10 ledger), `TCB.md` (the trust boundary), `known-gaps.md`
(anything unproved or deliberately limited), `certificate-v1.md` (the frozen
wire format), the roadmap, and the plan.

**Contribution.** `THEOREMS.md` is the contract T5 will be judged against;
`certificate-v1.md` is the interface the Haskell analyzer will target;
`known-gaps.md` is the honest record of limitations.

**Cost/risk.** They are partly stale at M2: `TCB.md` says "M1 status" and omits
the interval modules; `known-gaps.md`'s table says "none" while its own
limitations paragraph describes M2; `THEOREMS.md` says T4 is `in-progress`
without listing which parts are proved; `Interval.lean`'s header says transfer
lives in that file (it does not); `IntervalTransfer.lean` says read/len are top
"until M2.7" (M2.7 added a new layer rather than changing this one). See F7.

---

## 5. Architecture and flow

### 5.1 The full pipeline

```text
                    TRUSTED (Lean)                                  UNTRUSTED
  .imp ──parse(M4.5)──▶ Program ──compile(M1.6)──▶ CFG ──step/run(M1.6-1.7)──▶ Safe
                          │                        │
                          │                        └──edges(M1.8)──▶ List Edge
                          │                                              │
                          │                                              ▼
                          │                                    check(M3) ──▶ verdict
                          │                                         ▲
                          └──AST.json──▶ [Haskell M5] ──cert.json──▶ decode(M4)
                                             fixpoint/widening        (untrusted bytes)
```

The theorem that closes the loop is
`check_sound : check D p c = .ok → Program.safe p`.
The certificate supplies abstract states only; the obligations are derived from
the program and the edges. The Haskell side never contributes a verdict, only a
proposal.

### 5.2 M2's slice of the pipeline

M2 builds the domain column and the soundness fields that connect it
to the semantics:

| Layer | Type | What it adds | Soundness theorem | Used by |
|---|---|---|---|---|
| `I32` | `I32` | machine integers, checked arithmetic | `add?_sound`, … | everything |
| `Interval` | `Interval` | box, membership, inclusion, join, top | `ble_sound`, `join_sound`, `top_sound` | transfer |
| `Env`/`Abs` | `Var → Interval`, `Abs` | one box per variable; one per array | `evalExpr_sound`, `assign_sound`, `evalExprAbs_sound` | transfer |
| `Abs` (support) | `Abs` | support-restricted concretisation and transfer | `evalExprAbsOn_sound`, `assignAbsOn_sound`, `storeAbsOn_sound`, `bleAbs_sound`, `joinAbs_sound`, `transferAbs_sound` | the instance |
| `CertDomain` | record | the assembled domain | the four soundness fields | T5 (M3) |

The dependency direction is acyclic:

```text
I32 → Interval → IntervalTransfer → IntervalArrays → IntervalInstance
                                                        │
Semantics ──────────────────────────────────────────────┘
Domain (CertDomain) ─────────────────────────────────────┘
```

`Domain.lean` imports `Semantics` (for `EdgeCmd`/`State`), not the other way
round; the interval modules import `Domain` only at the last step. That is the
right layering: the kernel interface does not depend on any particular domain.

### 5.3 The checker's flow (what M3 adds)

```text
cert.json ──decode(M4, total)──▶ Certificate { entry, states }
                                        │
      ┌─────────────────────────────────┼─────────────────────────────────┐
      ▼                                 ▼                                 ▼
  init obligation                 edge obligations                 safety obligations
  γ(entry) ⊇ Init                 ∀e: γ(transfer e (I e.src))       γ(I p) ⊨ safePred(p)
      │                           ⊆ γ(I e.dst)                      │
      └─────────────────────────────────┴─────────────────────────────────┘
                                        ▼
                                .ok  ⇒  Program.safe   (T5)
```

Every box is one `ble` call; every safety check is one `entails` call; there is
no search. The missing pieces are marked in F1: `init`, `entails`, `bot`, and
`P`-preservation.

### 5.4 The trust boundary

**Trusted:** `I32`, `Semantics` (AST, compiler, `eval`, `step`, `run`, `Safe`,
`edges`, `WF`), the interval domain (all four modules), the future parser,
decoder, checker, and the audit. **Untrusted:** the Haskell analyzer, the Python
harness, and every certificate byte.

A bug in the untrusted side yields a rejected certificate, not a wrong verdict; a
bug in the trusted side changes what "safe" means. M2 adds ~1,100 lines to the
trusted side. The audit is the only mechanism that proves the trusted proofs
rest on nothing extra, and it currently covers only the M1 half.

### 5.5 What T5 needs from M2

| T5 needs | Supplied by M2 | Still missing |
|---|---|---|
| Base case: `State.init p ∈ γ(entry)` | `State.init`, `get_init`, `memAt_init`, `top_sound` | an `init : Abs` and `init_sound` (or an `initAbs` + `POn`-init lemma) |
| Every actual step matches an edge | `step_edge` (M1) | — |
| Edge obligation transports the invariant | `transfer`, `ble`, `transfer_sound`, `ble_sound` | `P`-preservation (the `P s'` premise is assumed) |
| The step cannot fail | `eval`/`exec` hazard cases, `idxWithin_sound` | `entails` + `entails_sound` for asserts, divisors, and indices |
| Unreachable points | `top` default (missing state) | a `bot` for v1's explicit unreachable state |
| The run is a finite prefix | `safe_iff_exists` (M1) | — |
| T1 determinism | `step_det` (M1) | — |
| T8 acceptance-completeness | `ble` soundness | `ble_complete` and a decision on `entails` completeness |

This table is the real interface of M2. Five of its rows are not yet supplied;
they are the first work of M3, not details to discover inside T5.

### 5.6 A concrete end-to-end trace

The simple program from §1.5, with the certificate table and each check made
explicit. `D` is `intervalDomain (fun _ => 0) ["x"] []`.

| Point | Instruction | Claimed box | Check |
|---|---|---|---|
| 0 | `x := 0` | `x ∈ [0,0]` | init: `[0,0]` contains `x=0` ✓ |
| 1 | `x := x + 1` | `x ∈ [0,0]` | edge 0→1: `[0,0]` after `x:=0` ⊆ `[0,0]` ✓ |
| 2 | `assert x == 1` | `x ∈ [1,1]` | edge 1→2: `[0,0] + [1,1] = [1,1]` ⊆ `[1,1]` ✓ |
| 3 | halt | `x ∈ [1,1]` | safety at 2: `[1,1]` entails `x == 1` ✓ (needs M3) |

This is the "hello world" of the kernel. It uses `add`, `ble`, `top`, and the
init base; it does not use `join`, arrays, division, or guards. It is the right
first M3 golden test.

### 5.7 The two showcase traces, reproduced

The review reproduced both failures with a temporary Lean file (not checked in;
see §11). The outputs are the evidence for F3.

**Division.** The certificate-v1 §13 example, with the claimed state at point 3
(`x ∈ [1,1]`, `y ∈ [10,10]`) and the transfer of `y := 10 / x` from point 2:

```text
#eval transferred.vars "x" == between 1 1   -- true
#eval transferred.vars "y" == Interval.top  -- true
#eval D.ble transferred s3                  -- false
#eval D.ble s3 transferred                  -- true
```

The transfer leaves `y` at `top` because `evalExpr` maps `.div` to `top`. The
edge obligation `ble transferred s3` is false, so the worked example is
rejected. A singleton/constant division rule would make the transfer `y ∈
[10,10]` and the obligation true.

**Loop.** The `examples/safe.imp` loop, with the head invariant `x ∈ [0,3]`:

```text
#eval bodyEntry.vars "x" == between 0 3     -- true   (assume is the identity)
#eval bodyExit.vars "x"  == between 1 4     -- true   (after x := x + 1)
#eval D.ble bodyExit head                   -- false  (back edge fails)
```

With guard refinement, `bodyEntry` would be `[0,2]`, `bodyExit` would be `[1,3]`,
and `ble [1,3] [0,3]` would be true. The identity `assume` is the cause.

Neither failure is a soundness bug. Both are precision gaps, and both are in the
demo path: M5's G2 and M10's benchmark families depend on them, and M3.9 must
pick a straight-line program (like §5.6) if it wants a golden accept before the
fix. They are the reason this review says "sound but not demo-complete".

---

## 6. Decisions and alternatives

### 6.1 `CertDomain` carries a program-state invariant `P`

**Decision.** The structure is parameterised by `P : State → Prop`, and every
soundness field is conditioned on `P`. For the interval instance, `P = POn
lengths`, "every array has its declared length".

**Why.** `top_sound` cannot hold for arbitrary states: an interval cannot describe
an array's length, so `γ top` cannot contain a state whose arrays have the wrong
size. The program's fixed array lengths are a *precondition*, not an abstract
fact. Threading `P` keeps `gamma` a simple predicate and `top` a simple value,
and lets any domain assume the program invariant it needs.

**Alternatives.**

- **Put lengths into `Abs`.** Then `top` is "unbounded vars + exact lengths",
  `ble` compares lengths, and the certificate must encode lengths per state
  (bytes grow by |arrays| × states) or via a global table. `gamma` becomes
  self-contained and the T5 base case is easier, but every domain (product,
  octagon) must carry lengths, and the v1 state encoding would change. Rejected:
  costs bytes and genericity.
- **`gamma : Abs → State → Prop` with `top` meaning "all reachable states".**
  Not expressible without a reachability predicate; you end up with `P` anyway.
- **Drop `P`; restrict `Safe` to well-formed states.** Same invariant, implicit;
  `transfer_sound` still needs it at successors, and the checker would have to
  re-prove it. No gain.
- **Use `Set State` and intersect with `P`.** Mathlib, rejected by D2.

**Cost.** Every field carries `P`; `transfer_sound` takes `P s'` as a premise;
T5 needs a `P`-preservation lemma. The last cost was not paid (F1). The M6
product's `P` will be `P₁ ∧ P₂`, which is fine but should be noted in the plan's
"product is just an instance" claim.

**Verdict.** Right shape. The missing preservation obligation is the defect.

### 6.2 `gamma` is a predicate, not a `Set`

**Decision.** `gamma : Abs → State → Prop`; `gamma i v` is the plan's
`v ∈ γ i`. `⊆` is `∀ s, gamma a s → gamma b s`.

**Why.** The tree is Mathlib-free (D2). `Set α` is a function `α → Prop` anyway,
so the predicate form loses no expressiveness; it removes a dependency, and every
lemma is a direct statement about the real thing. The checker's `ble` is the
executable counterpart, bridged by `ble_sound`.

**Alternatives.** Vendor a minimal `Set` abbrev plus notation (cosmetic; the
proofs are the same); depend on Mathlib (rejected); use finite sets (the state
space is infinite). No serious alternative.

**Cost.** No set algebra; `ble_sound` takes an explicit state argument; `join_sound`
is pointwise. These are minor.

**Verdict.** Right; the abstraction is the same and the TCB is smaller.

### 6.3 The interval representation, and the two constructors

**Decision.** `Interval = bot | itv (lo : Option I32) (hi : Option I32) (valid :
loLeHi lo hi)`. `ofBounds?` is the checked constructor (inverted finite bounds →
`none`); `ofBounds` is the normalising one (→ `bot`). `top = itv none none`.

**Why.** The validity proof makes an inverted interval unrepresentable inside the
tree, so `bot` is the unique empty interval and every match is total. `bot` is a
*value*, so the abstract state can be `Var → Interval` (total), with no `Option`
per variable. The two constructors are a security boundary: the decoder must turn
`lo > hi` into `Diagnostic.malformed` (T10), not silently into `bot`, while
internal arithmetic wants normalisation. `certificate-v1.md` §5.1 calls the
ill-formed interval "the classic soundness trap" — `ble` on `[5,3]` would answer
"contained in everything" if it were allowed.

**Alternatives.**

- **`lo hi : I32` with a `lo ≤ hi` proof, and `Option Interval` for bottom.**
  Pushes `Option` into every container and every `ble`/`join`; the certificate's
  `bot` is per-point, not per-variable, so a whole-state bot plus per-variable
  options is awkward. No gain.
- **`lo hi : Int` without validity, `lo > hi` = empty.** Two representations of
  empty; the decoder must special-case; the `ble` trap is live. Rejected.
- **`lo hi : Option Int` without a proof, smart constructors only.** Every lemma
  carries `lo ≤ hi` as a side condition. Rejected for proof ergonomics.

**Cost.** `DecidableEq`/`Repr` deriving with a proof field; a `loLeHi` decidable
instance; `toInterval`'s validity proof was written with `simp`, which is the
root of the `Classical.choice` footprint (F2). The fix is one line:
`(by exact Int.le_refl n.val)`.

**Verdict.** Right; fix the proof term.

### 6.4 Convex-hull join

**Decision.** `join` is the convex hull: the weaker lower bound and the stronger
upper bound; `bot` is the identity; unbounded sides absorb.

**Why.** Intervals form a lattice, and the hull is the least upper bound. The
analyzer needs a join to merge states at control-flow merges; the checker's
`join_sound` field is what makes the domain usable by the generic product
combinator. The hull is the standard interval join and is what the product/label
machinery builds on.

**Alternatives.**

- **Disjunctive completion** (a set of intervals). Exact for unions, but
  inclusion becomes combinatorial (O1) and the checker would need a matching
  search, violating R4. This is the road the project explicitly routes around.
- **Reduced product with a label domain (M9).** Recovers path sensitivity without
  changing the interval join; the labels keep the two boxes apart instead of
  joining them. This is the project's chosen route.
- **A product of two intervals** (keep both). That is a product, not a join; it
  would need a reduction to be useful, which is M8.

**Cost.** `[0,1] ⊔ [3,4] = [0,4]` contains 2; assertions that need the gap are
unprovable. That is the precision loss labels address, and it is measured, not
hidden.

**Verdict.** Right; the loss is the motivation for C3, not a bug.

### 6.5 Overflow collapses to `top`

**Decision.** If computing a finite endpoint leaves the signed 32-bit range, the
whole result is `top`. (`addLower?`/`addUpper?` return `none`; `add`/`sub` match
to `top`.)

**Why.** It is sound (top contains every value), it is one line to state, and it
keeps the T4c proof short. The checker's safety obligations separately rule out
overflow on accepted executions: the safety check uses the pre-state box, not
the transferred result. A program that overflows is unsafe, and the checker
rejects it; a program that cannot overflow is proved safe from the pre-state.

**Alternatives.**

- **Saturate to `[i32Min, i32Max]`.** Same effect as top, more code and a
  misleadingly precise-looking box; no gain.
- **Wrap the endpoints modulo 2^32.** Unsound for the safety property: an
  overflow is a *failure*, not a wrap. This is the one alternative that would be
  a real bug.
- **Keep an "overflow happened" flag** (a product with an error domain). More
  precise — you could prove that the operation *must* fail — but more proof work
  and not needed for safety. A candidate for a future domain.
- **Return `none` from `transfer`.** Complicates the type and every caller;
  `transfer` is total by design.

**Cost.** All precision after a possible overflow is lost; a later assertion
about the result cannot be proved. The safety check itself still works from the
pre-state.

**Verdict.** Right for M2; a deliberate precision limitation, documented.

### 6.6 Precision staging: `+`/`−` exact, `×`/`÷` top

**Decision.** `add` and `sub` are exact over the abstract bounds; `mul` and
`div` return `top`; array read/len are `top` in `IntervalTransfer` and precise in
`IntervalArrays`/`IntervalInstance` when the array is in the support.

**Why.** Addition and subtraction are the common cases for loop counters and
array indices, and their proofs are short. Multiplication needs four endpoint
products and sign case analysis; division needs sign cases, zero, truncation, and
`min / −1`. M2's goal was the first *sound* domain, not maximum precision; the
conservative transfer makes T4c true and keeps the proof surface small.

**Alternatives.**

- **Full interval multiplication now** (~50 lines plus proof). Feasible, but it
  would have displaced the array work; the proof is longer but not hard.
- **Full division now.** Harder: the divisor's box must exclude zero, the result
  endpoints depend on signs and truncation, and `min / −1` is a special case.
  A later milestone.
- **Singleton/constant folding only.** If both operands are singletons, compute
  exactly; otherwise `top`. Cheap (~20 lines) and enough for the canonical
  `10 / [1,1]` example. **Recommended as the first precision fix.**
- **Symbolic/relational division.** Out of scope.

**Cost.** The canonical worked example (`y := 10 / x; assert y == 10`) is not
certifiable; the "straight-line arithmetic" and "small kernels" benchmark
families will underperform; any assertion about a product fails. The roadmap's
M2.6 says "binop"; the delivered scope is only `+`/`−`.

**Verdict.** Defensible for M2 *if recorded as a deviation* (it is, in
`known-gaps.md`), but the singleton/constant rule should land before M3.9/M5 so
the demo is not blocked on full division.

### 6.7 Arrays as one summary per array

**Decision.** The abstract state has `mem : Arr → Interval`, one interval
covering **every cell** of each array. A read returns the array's interval; `len`
returns the declared length; `idxWithin` checks the index; a store sets the
written array to `top`.

**Why.** Array bounds are a safety property, and the index box plus the declared
length are all the bounds check needs. Per-cell intervals would be `Arr → Nat →
Interval`, a huge abstract state and certificate, and a much bigger transfer
proof for no bounds benefit. The summary is the smallest sound abstraction that
supports `read`/`len` and bounds.

**Alternatives.**

- **Per-cell intervals.** Precise for contents, but the state and certificate
  grow with the total number of cells; the transfer for `store` becomes a
  pointwise update with a join; the certificate format would need to encode
  cells. Rejected for M2.
- **No array abstraction** (all reads `top`). Sound and simpler, but `len` and
  read precision would be lost; bounds could still be checked from the index.
  A fallback if the format cannot carry `mem`.
- **A relational array domain** (contents related to indices). Out of scope.

**Cost.** Store → `top` loses contents; assertions about array values cannot be
proved; the `mem` component is not in v1 (F5). Bounds are unaffected.

**Verdict.** Right for bounds; the v1-format mismatch must be settled before M4.

### 6.8 Smaller decisions

| Decision | Why | Alternatives | Cost / note |
|---|---|---|---|
| Support-restricted instance (`GammaOn`, `evalExprAbsOn` over `vars`/`arrays` lists) | The certificate is a finite map; the checker knows the program's names; unknown names evaluate to `top`, so no support proof is needed on `Abs` | Constrain all variables/arrays (`AbsSound`); add a `Support` predicate; use finite maps | Leaves two transfer towers (F6); `POn` still quantifies all arrays |
| `transfer : EdgeCmd → Abs → Abs` | The checker's obligations are edge-indexed; a branch is one step / two edges; `Cmd` has no `assume` case | `transfer : Cmd` plus a separate `guardRefine`; a relational transfer | `assume` is currently the identity (F3); the interface is right |
| `ble : Bool` plus a reflection lemma (D7) | Predictable compiled cost; explicit reflection; the checker must run | `Decidable` everywhere; `Prop` only with `decide` | More lemmas; the checker calls `ble` |
| No Mathlib; local `funUpdate`/list lemmas | Small TCB, fast build, one language (D2) | Mathlib | A few trusted utility lemmas to review |
| JSON certificates (D4) | Human-readable; LLM/tool-friendly; verbosity is the measured cost | S-expressions, Protobuf, CBOR | Decoder must be total (M4) |
| Haskell analyzer (D3) | Architectural trust boundary; good for fixpoints | Lean/Python/OCaml | Two implementations to keep in sync |
| `#guard` tests, one file per subtask | No dependencies; a false expectation fails the build | Lean test framework; Python runner | Manual CI list; value-biased (F8) |
| One commit per subtask, one branch for the milestone | Bisectable history; each commit green | Branch per subtask (rejected: merge conflicts) | `feat/domain-interval` is 9 ahead of `main`, unmerged (F7) |

The two decisions *not* made at M2 are the important ones:

- **No `entails` field.** `certificate-v1.md` §12.6 asked for it before M2.6;
  `idxWithin` is a specialized helper, not the general safety test. This is F1.
- **No `P`-preservation obligation.** `transfer_sound` assumes `P s'`; T5 needs
  to prove it. This is also F1.

**What I would do differently with hindsight.** Settle the `CertDomain`
interface *before* building the instance. The instance is sound, but it was built
against a structure the checker cannot yet consume; adding `entails`, `init`,
`bot`, and `P_step` afterwards means touching `Domain.lean`, the instance, the
tests, and `THEOREMS.md`. The cost is a day now and grows at M3, where the
pressure is on T5.

---

## 7. Findings

Findings are ordered by risk to the project, not by effort. Each has a concrete
next step.

### F1 — **High**: the `CertDomain` interface is missing four operations T5 needs

`CertDomain` provides `P`, `Abs`, `gamma`, `ble`, `top`, `transfer`, `join` and
their soundness fields. The checker's three obligation families need more:

| Checker need | Interface field | Status |
|---|---|---|
| Init: `γ(entry) ⊇ Init` | `init : Abs`, `init_sound : P (State.init p) → gamma init (State.init p)` | **missing** |
| Edge: `γ(transfer e (I p)) ⊆ γ(I q)` | `ble`, `transfer`, `ble_sound`, `transfer_sound` | present, but `transfer_sound` assumes `P s'` |
| Safety: `γ(I p) ⊨ safePred(p)` | `entails : Abs → BExp → Bool`, `entails_sound` | **missing** |
| v1 `bot` state | `bot : Abs`, `bot_sound` (or an `Option Abs` checker state) | **missing** |
| Induction invariant `P s` | `P_step : P s → EdgeCmd.exec c s = some s' → P s'` | **missing** |

Consequences:

- T5's statement `check D p c = .ok → Program.safe p` cannot be proved for an
  arbitrary `D : CertDomain` from the landed fields. M3 will either extend the
  structure (and redo the instance and its tests) or specialize `check` to
  intervals (weakening the genericity claim C1 — the kernel would no longer be
  domain-generic).
- The safety family is the most concrete gap: `ble` cannot express `x ≠ 0`, and
  `idxWithin` is an interval-specific helper, not a `CertDomain` operation.
  `certificate-v1.md` §12.6 already identified this and said "decide the exact
  shape before M2.6"; M2.6 passed without a decision.
- The init family is easy to miss because the certificate's entry state is often
  `top`; but a precise entry state (`x = 0`) needs an abstract `init` to check
  against, and the domain has no `init`.
- The v1 format has a whole-state `{"kind":"bot"}`. A generic decoder cannot
  construct a bottom `Abs` without a `bot` field; an `Option Abs` state in the
  checker is the alternative, but that is a checker design decision, not a domain
  one.

**Next step.** Amend `Domain.lean` before M3.1 with `init`/`init_sound`,
`entails`/`entails_sound`, `bot`/`bot_sound` (or an explicit `Option Abs` design
note), and `P_step` (or a `P`-preservation theorem for the instance). Prove them
for the interval instance. Update `THEOREMS.md` T4/T5 and `certificate-v1.md`
§12.6. This is the highest-value hour in the project right now.

### F2 — **High**: the audit gate is M1-only, and 15 M2 lemmas carry `Classical.choice`

`Audit.lean` imports `CertCore.Semantics` and prints seven M1 lemmas; it does not
import `CertCore.Domain.IntervalInstance`. The M2 footprint, measured with
`#print axioms` on all 43 proved lemmas:

```text
15 lemmas depend on [propext, Classical.choice, Quot.sound]:
  assign_sound, assignAbs_sound, assignAbsOn_sound,
  evalExpr_sound, evalExprAbs_sound, evalExprAbsOn_sound,
  gamma_toInterval, gamma_toInterval_iff,
  join_sound, joinAbs_sound,
  leLo_minLo_left, leLo_minLo_right,
  leHi_maxHi_left, leHi_maxHi_right,
  transferAbs_sound
```

The milestone's exit criterion names `ble_sound`, which is clean; the instance's
`transferAbs_sound` — the field T5 consumes — is not. The project's policy
(`Audit.lean` header, `TCB.md`, plan D10) says every line should be `[propext,
Quot.sound]` or smaller, and `Classical.choice` is called a soundness hole.
*It is not a soundness bug* — `Classical.choice` is a consistent classical axiom,
and the theorems are true — but it violates the stated contract, would fail the
planned M11.4 gate, and makes the trusted proofs non-constructive for no reason.

The footprint has two small roots, both verified:

1. **`Interval.toInterval`'s validity proof** is `(by simp [loLeHi])`. The
   definition itself depends on `Classical.choice`, so every theorem that unfolds
   it (`gamma_toInterval`, `evalExpr_sound`, the whole `assign`/`transfer` chain)
   inherits. Replacing it with `(by exact Int.le_refl n.val)` makes `toInterval`
   depend only on `[propext]`, and `gamma_toInterval` on `[propext]` (verified).
2. **The `minLo`/`maxHi` order lemmas** use `by_cases h … <;> simp [minLo, leLo,
   h] <;> omega`; `simp` with a positive `if` hypothesis introduces
   `Classical.choice`. Replacing the idiom with `dsimp only [minLo]; split <;>
   simp only [leLo, decide_eq_true_eq] <;> omega` makes `leLo_minLo_left` depend
   only on `[propext, Quot.sound]` (verified).

Fixing the two roots should clean most of the 15 (the chain is
`toInterval` → `evalExpr` → `assign` → `transfer`; and `minLo`/`maxHi` →
`join`). Re-run the full audit afterwards to confirm no third root remains.

**Next step.** Fix the two roots; extend `Audit.lean` to import
`IntervalInstance` and print every M2 theorem; add a CI comparison that fails on
`Classical.choice` or `sorryAx` (this is M11.4, brought forward because the
trusted tree has grown substantially). Then update the audit header and `TCB.md`.

### F3 — **High**: the two showcase programs are not certifiable

The domain is sound but too weak for the programs the project promises to demo.
Reproduction in §5.7:

- **Division:** `y := 10 / x` with `x ∈ [1,1]` transfers to `y = top`, so the
  edge obligation to the claimed `y ∈ [10,10]` at the assert fails. The
  certificate-v1 §13 worked example is rejected.
- **Loop:** the head invariant `x ∈ [0,3]` cannot be re-established from the body,
  because `assume` is the identity, so the body starts at `[0,3]` and ends at
  `[1,4]`; the back edge `[1,4] ⊆ [0,3]` is false. `examples/safe.imp` is
  rejected.

Neither is a soundness bug; both are precision. But the demo path is blocked:
M5's G2 and M10's benchmark families will need them, and M3.9's golden accept
test must either pick a straight-line program or wait for the fix.

**Next step.** (a) Implement guard refinement for the single-variable comparisons
in `assume` edges: `x < c` true → `[lo, min(hi, c−1)]`, false → `[max(lo, c),
hi]`, similarly for `≤, >, ≥, =, ≠`; conjunction intersects; disjunction joins
(or is skipped). This is a `refine : Abs → BExp → Bool → Abs` with a soundness
proof against `EdgeCmd.exec`, and it plugs into `transferAbs`'s `assume` case.
(b) Implement division for singleton/constant divisors; full division can wait.
(c) Add a `Tests/Demo.lean` that builds the two certificate tables and asserts
the edge obligations (it will fail until (a)/(b) land — mark it expected-fail or
land it with the fix). This is the M2 equivalent of M1's branch-tail regression.

### F4 — **Medium/High**: `ble` completeness and the T8 contract

`ble` is proved sound, not complete. T8 `encode_accepts : IsPostFixpoint p I →
check D p (encode p I) = .ok` needs two things M2 does not supply:

1. **`ble_complete`:** if `γ a ⊆ γ b` then `ble a b = true`. For intervals this is
   a short case analysis and should be proved. Without it, a genuine
   post-fixpoint can be rejected, and T8 cannot be proved.
2. **A decision on `entails` completeness.** A convex interval can be covered by
   a union of convex sets without being contained in any one of them (e.g., an
   `or` of two comparisons whose union covers the interval). A three-valued
   `entails` that evaluates disjuncts separately is sound but not complete. T8 as
   written presumes completeness for every safety predicate, which is too strong
   for a convex domain.

**Next step.** Prove `ble_complete` for intervals; state T8 with an explicit
`InvariantEntailsSafety` hypothesis (or restrict it to predicates the test
decides exactly); document the completeness limitation in `THEOREMS.md` and the
paper's threats-to-validity section. This is a theorem-contract issue, not a code
bug, and it is cheaper to settle before M3.7 than after.

### F5 — **Medium**: the v1 format has no array-memory field

`IntervalArrays.Abs` has `mem : Arr → Interval`, and `GammaOn` constrains it.
`certificate-v1.md` §5.1 encodes a state as `{"kind":"itv","vars":{…}}` only; there
is no array component. A v1 certificate therefore cannot carry array contents, so
the decoder must set `mem` to `top`, and M2.7's precise read transfer is
unreachable end-to-end. Array **bounds** still work: `idxWithin` uses the index
box and the declared length, not `mem`.

**Next step.** Decide before M4.1: either (a) extend v1 with an optional `mem`
map (absent array = `top`; the decoder is strict about unknown fields, so this
needs a format rule or a version bump), or (b) declare v1 arrays bounds-only and
set `mem` to `top` in the decoder, documenting that array contents are a future
format feature. Add the decision to `certificate-v1.md` §12 and a test in
`Tests/Arrays.lean`/`Tests/Instance.lean` that pins the chosen behaviour.

### F6 — **Medium**: two of the three transfer towers are not on the final path

The tree contains three evaluators:

- `IntervalTransfer.evalExpr`/`assign` (the M2.6 `Env` layer);
- `IntervalArrays.evalExprAbs`/`assignAbs` plus `AbsSound` (the M2.7 layer);
- `IntervalInstance.evalExprAbsOn`/`assignAbsOn` plus `GammaOn` (the M2.8 layer,
  used by the instance).

The final instance uses the third; the first two are used by tests and by each
other (the array layer calls `add`/`sub` from the transfer layer, but not
`evalExpr`). `AbsSound`/`evalExprAbs_sound`/`assignAbs_sound` are used only by
`Tests/Arrays.lean`. This is roughly 400 lines of trusted code that does not participate
in the final proof, and it doubles the proof surface an auditor must read.

**Next step.** Consolidate: either build the instance on the unrestricted
`AbsSound`/`evalExprAbs` (and delete the `On` variants), or make the `On` variants
the only path and move the test-only `AbsSound` family out of the trusted
library. If both are kept for staging clarity, mark the unused layer as
"test-only, not in the TCB" and exclude it from the audit. Do not keep two
trusted transfer semantics with no proof that they agree.

### F7 — **Low/Medium**: documentation and merge state have not caught up

- `TCB.md` says "this is the M1 status" and its table omits the four interval
  modules; the trusted tree has grown by ~1,100 lines.
- `known-gaps.md`'s table says "none — the M1 tree has no `sorry`", while the
  same file's limitations paragraph describes M2.8's conservative transfer.
- `THEOREMS.md` says T4 is `in-progress`; T4a, T4b, top, T4c and the array/instance
  fields are proved; only `entails_sound` is missing. Say which parts.
- `Audit.lean`'s header says "At M1 the script prints…"; `Cli.lean` and the
  README quick start still print "M1 semantics core".
- `Interval.lean`'s header says "The gamma function, inclusion, join and transfer
  are M2.2–M2.6 and live in this file as they land" — transfer is in
  `IntervalTransfer.lean`; the file is M2.1–M2.5.
- `IntervalTransfer.lean` says read/len are top "until M2.7" — M2.7 added a new
  layer, it did not change this one.
- `main` is at M1; `feat/domain-interval` is nine commits ahead and unmerged;
  CI on `main` has not run the M2 tests, and `Audit.lean` is M1-only.

(This review has been linked from the README's Documents list; the rest of the
drift remains.)

**Next step.** Update the TCB table (add the interval modules and their trust
status), the known-gaps table, the T4 status, the audit header, the CLI/README
version line, and the two module headers. Add this review to the README Documents
list. Open the PR and let CI run before merging.

### F8 — **Low**: test coverage is value-biased

Nineteen files and 256 `#guard`s are strong on values. There is no test for:

- the instance's `assume` transfer (would have caught F3's loop half);
- `POn` at `State.init p` (would have caught F1's init gap);
- `ble` completeness (the negative direction);
- `entails` (it does not exist);
- an end-to-end certificate (the checker does not exist yet);
- the v1 `bot` state / `mem` encoding (F5).

**Next step.** Add `Tests/Demo.lean` (the two showcase tables, expected-fail until
F3 is fixed), a `POn`/`init` test, and a `ble_complete` test once the theorem
exists. The M1 review's lesson was that biased examples hide bugs; the M2 version
of that lesson is that value tests hide interface gaps.

---

## 8. What M2 actually establishes

It is worth being precise about the assurance level, because "M2 reached" can
sound like more than it is.

| Claim | Proved? | Where / note |
|---|---|---|
| `I32` checked arithmetic is sound; wrap agrees when checked succeeds | **yes** | M1, inherited; tested |
| Interval membership/inclusion/join/top are sound | **yes** | `gamma_*`, `ble_sound`, `join_sound`, `top_sound` |
| Arithmetic transfer (`+`/`−`) is sound; `×`/`÷`/read/len are `top` at M2.6 | **yes** | `evalExpr_sound`, `assign_sound`; conservative cases are `top` |
| Array read/len are sound; `idxWithin` implies the concrete bounds | **yes** | `evalExprAbs_sound`, `idxWithin_sound` |
| The assembled `CertDomain` has all its fields | **yes** | `intervalDomain`; the fields typecheck |
| The `CertDomain` interface is sufficient for T5 | **no** | F1: missing `init`, `entails`, `bot`, `P_step` |
| The domain can certify `examples/safe.imp` | **no** | F3: no guard refinement |
| The domain can certify the certificate-v1 §13 example | **no** | F3: division is `top` |
| `ble` is complete (needed for T8) | **no** | F4 |
| The audit covers the M2 trusted code | **no** | F2: `Audit.lean` imports `Semantics` only |
| A program has been proved safe end-to-end | **no** | M3's checker does not exist yet |
| The parser/decoder exist | **no** | M4 |

**No program has been checked end-to-end at M2.** What M2 proves is that the
first domain is sound: every operation over-approximates, and the instance's
soundness fields typecheck. That is the right thing to prove before the checker,
and it is why the T4 proofs matter more than their length suggests.

The manual M2 axiom check is **not** clean: 15 of 43 lemmas carry
`Classical.choice`. The domain is still sound — `Classical.choice` does not make
a theorem false — but the project's audit contract is not met, and the exit
criterion's sample (`ble_sound`) happened to be one of the clean ones.

---

## 9. Handoff checklist for M3/M4

Ordered by risk, not by effort. The first four are the real exit work.

1. **Settle the `CertDomain` interface** (F1): add `init`/`init_sound`,
   `entails`/`entails_sound`, `bot`/`bot_sound` (or an `Option Abs` note), and
   `P_step` (or a `POn`-preservation theorem). Prove them for the interval
   instance. Update `THEOREMS.md` T4/T5 and `certificate-v1.md` §12.6.
2. **Fix the two `Classical.choice` roots and extend the audit** (F2):
   `toInterval`'s proof and the `minLo`/`maxHi` lemmas; import
   `IntervalInstance` in `Audit.lean`; add the CI comparison. Re-run the full
   audit and record the footprint.
3. **Add guard refinement and singleton/constant division** (F3): enough to
   certify `examples/safe.imp` and the certificate-v1 §13 example. Add
   `Tests/Demo.lean`.
4. **Prove `ble_complete` and settle T8's statement** (F4):
   `InvariantEntailsSafety` as an explicit hypothesis, with the completeness
   limitation documented.
5. **Decide the v1 `mem` encoding** (F5) before M4.1: optional `mem` map or
   bounds-only arrays with `mem = top` in the decoder.
6. **Consolidate the transfer tower** (F6): one trusted evaluator, or a clear
   test-only marker for the unused one.
7. **Update the docs and merge** (F7): TCB table, known-gaps table, T4 status,
   audit/CLI headers, README Documents; open the PR; let CI run; merge after 1–2.
8. **Add the missing interface tests** (F8): `assume`, `POn`-init, `ble`
   completeness, `bot`/`mem`, and the demo tables.

The first four are the M3 opening, not cleanup. The rest are cheap and pay for
themselves before M3.7.

---

## 10. Bottom line

M2 is a good milestone. The hard conceptual work — represent intervals with a
canonical empty case, prove inclusion/join/top against a predicate-valued
`gamma`, transfer arithmetic and arrays, and assemble a `CertDomain` — is done,
in about 1,100 lines of readable Lean, with 256 executable checks and no
`sorry`. No soundness bug was found. The design decisions (the `P` parameter,
the predicate `gamma`, the checked/normalising constructors, the convex hull,
the overflow-to-top policy, the support restriction, `EdgeCmd` transfer) are
defensible and documented.

But the milestone is not demo-complete or audit-clean. The `CertDomain` interface
is missing the operations the checker needs; the two showcase programs are
rejected for precision reasons; 15 M2 lemmas carry `Classical.choice`; the audit
does not import the new trusted code; and the docs still describe an M1 tree.
The reassuring part is that the fixes are small and well-scoped: two proof terms,
one script change, one interface extension, one guard-refinement pass, one
singleton-division pass. If they land before M3 begins, T5 has a clean path. If
M2 is declared done now, M3 will meet them as proof obligations under gate
pressure — and the interface gap will look like a kernel design flaw rather than
a missing field.

**Verdict: merge after F1's decision is recorded and F2's fixes are in; start M3
with F1, F3, and F4 in that order.**

---

## 11. Reproduction commands and review evidence

```console
$ lake build
Build completed successfully (29 jobs).

$ lake env lean lean/Tests/I32.lean        # and each of the other 18 test files
# exit 0

$ Get-ChildItem -Recurse lean -Filter *.lean | Select-String -Pattern '\bsorry\b'
# none

$ lake env lean lean/CertCore/Audit.lean
'CertCore.I32.ofIntWrap_agrees' depends on axioms: [propext, Quot.sound]
'CertCore.CFG.step_det' depends on axioms: [propext, Quot.sound]
'CertCore.CFG.safe_iff' depends on axioms: [propext, Quot.sound]
'CertCore.CFG.safe_iff_exists' depends on axioms: [propext, Quot.sound]
'CertCore.Program.compile_wf' depends on axioms: [propext, Quot.sound]
'CertCore.Program.compileChecked_wf' depends on axioms: [propext, Quot.sound]
'CertCore.CFG.step_edge' depends on axioms: [propext, Quot.sound]
```

The M2 footprint was measured with a temporary file (not checked in) that
imports `CertCore.Domain.IntervalInstance` and runs `#print axioms` on all 43
proved lemmas. The two showcase traces were measured with a temporary file that
builds the `intervalDomain` and evaluates the `ble`/transfer calls shown in §5.7.
The `#eval` outputs quoted there are the actual outputs.

**The ten unit cases** (`Tests/IntervalUnit.lean`) pin:

| # | Case | Expected |
|---|---|---|
| 1 | singleton `[5,5]` contains 5, not 4 | membership |
| 2 | `[2,8] ⊆ [0,10]`, not the reverse | inclusion |
| 3 | `join [0,1] [3,4] = [0,4]` | convex hull |
| 4 | `top` contains 42; `[−100,100] ⊆ top` | top |
| 5 | `[1,2] + [3,4] = [4,6]` | addition |
| 6 | `[1,2] − [3,4] = [−3,−1]` | subtraction |
| 7 | `max + 1` overflows → `top` | overflow policy |
| 8 | `read 0` of `mem 0 = [10,20]` → `[10,20]` | array read |
| 9 | `len` of a length-2 array → `[2,2]` | array length |
| 10 | `idxWithin [0,1] 2` true; `[0,2] 2` false | bounds |

They are good value tests. They do not test the instance's `assume` edge, the
init base case, or an end-to-end certificate — which is exactly where the
milestone's gaps are (F8).

---

## 12. Post-review fix — F1 (2026-11-27, uncommitted)

F1 is fixed in the working tree on `feat/domain-interval`, pending review and
commit. The interface now has the checker's missing operations, and the interval
instance proves them.

**Interface (`Domain.lean`).** `CertDomain` gained:

- `P_step : P s → EdgeCmd.exec c s = some s' → P s'` (the induction invariant);
- `initOf : Program → Abs` and
  `init_sound : P (State.init p) → gamma (initOf p) (State.init p)` (the base case);
- `entails : Abs → BExp → Bool` and
  `entails_sound : entails a b = true → P s → gamma a s → evalB b s = some true`
  (truth *and* definedness).

`bot` is deliberately **not** a `CertDomain` field. The certificate's explicit
`{"kind":"bot"}` is a coverage marker; the checker stores a point's state as
`Option Abs` (`none` = bot) and skips its obligations. A `bot : Abs` field would
be unsound to add naively because a support-restricted `gamma` cannot distinguish
an all-`bot` state from a non-empty one when the support is empty.

**Instance (`IntervalInstance.lean`).** The new fields are proved as:

- `initOf_sound` — the initial abstract state is zero on the support; `POn` gives
  the array lengths; `Array.getD` on a zero-filled array is zero.
- `entailsAbs_sound` — a conservative three-valued evaluator. Expression
  evaluation returns `some` only when defined; `+`/`-` use guarded endpoint
  arithmetic (`addGuarded`/`subGuarded`) that returns `none` on an unbounded side
  or endpoint overflow; comparisons are decided from the endpoint boxes; `and`/
  `or` are strict, matching `evalB`. `*`, `/`, array reads and `len` return
  `none` (declined), so a safety predicate that needs them is rejected.
- `POn_step` — every `EdgeCmd.exec` preserves array lengths (`assign`/`assert`/
  `assume`/`skip` unchanged; `store` uses `Array.set`, whose size is preserved).

**Tests.** `lean/Tests/Interface.lean` pins `initOf`/`init_sound`,
`entails`/`entails_sound`, and `P_step`, including the `x + 1` overflow case
(`entails` declines when the box is `[max,max]`). All 20 test files pass; the
build is green with no warnings; no `sorry`.

**What this does not fix.** The new lemmas originally inherited
`Classical.choice` from the pre-existing `toInterval` proof (F2's first root),
so the audit-policy issue remained at the F1 checkpoint: `initOf_sound`,
`entailsAbs_sound`, `evalBGuarded_sound`, `evalExprGuarded_sound`, and the
assembled `intervalDomain` reported `[propext, Classical.choice, Quot.sound]`.
That was F2, not F1; it is fixed in §13. The `entails` conservatism is recorded
in `known-gaps.md` and `certificate-v1.md` §12.6.

---

## 13. Post-review fix — F2 (2026-11-27, uncommitted)

F2 is fixed in the same pass. The audit is now clean: every listed trusted
lemma depends only on `[propext, Quot.sound]` or smaller.

**Proof roots removed.**
- `Interval.toInterval`'s validity proof is `by exact Int.le_refl n.val` (was
  `by simp [loLeHi]`, which depended on `Classical.choice`).
- `gamma_toInterval` and `gamma_toInterval_iff` are constructive (explicit
  `lowerOk`/`upperOk` extraction rather than `simp`).
- The `minLo`/`maxHi` order lemmas use `dsimp only … ; split <;> simp only […,
  decide_eq_true_eq] <;> omega` instead of `by_cases … ; simp [h]`.
- The support-restricted evaluators (`evalExprAbsOn`, `evalExprGuarded`,
  `evalExprGuarded_sound`, `initAbs`, `initOf_sound`) use the computable
  `varMem`/`arrMem` functions instead of `if x ∈ vars` / `if a ∈ arrays`, whose
  `Decidable (List.Mem …)` instance pulled in classical choice. `varMem_sound`
  and `arrMem_sound` are the bridges back to membership for `GammaOn`.

**Audit and gate.**
- `Audit.lean` now imports `IntervalInstance` and prints the M1, M2, and F1
  footprint (36 lines: T1/T2, `compile_wf`, `step_edge`, `varMem_sound`, T4a/T4b/
  top, the arithmetic/array transfer, the instance fields, and the F1 fields).
- CI runs the audit and **fails** on `Classical.choice` or `sorryAx` (the M11.4
  gate, brought forward). This is the gate that was missing.

**Verification.** `lake env lean lean/CertCore/Audit.lean` prints only
`[propext, Quot.sound]` (or smaller); no `Classical.choice`, no `sorryAx`.
At the F2 checkpoint, all 20 test files passed; `POn_step`, `addGuarded_sound`,
`subGuarded_sound`, and `cmpGuarded_sound` were unchanged and clean.

---

## 14. Post-review fix — F3/F4 (2026-11-27)

**F3: the showcase programs.** The two programs the M2 review said were rejected
now close at the domain level.

- `Interval.meet` (with `maxLo`/`minHi`) intersects two boxes; `meet_sound` is
  proved in `IntervalTransfer` because its proof needs
  `gamma_ofBounds_of_lower_upper`.
- `Interval.div` is precise on singleton operands when `I32.div?` succeeds and
  `top` otherwise; `div_sound` is proved. The transfer evaluators use it, so
  `10 / [1,1] = [10,10]`.
- `IntervalInstance` gains `restrictHi`/`restrictLo`/`restrictEq` and the strict
  `restrictHiPred`/`restrictLoSucc` (with the `i32Min`/`i32Max` edge cases), then
  `refineVar` and `refineAbs`. The `assume` transfer now refines single-variable
  comparisons; conjunctions refine left-to-right, `not` flips the polarity, and
  disjunctions/non-variable comparisons are left unchanged. `refineVar_sound`
  and `refineAbs_sound` are proved and audit-clean.
- `Tests/Demo.lean` pins the two showpieces: the `safe.imp` loop with head
  `[0,3]` (body entry `[0,2]`, body exit `[1,3]`, exit `[3,3]`, assert
  `x == 3`), and the certificate-v1 §13 program (`10/[1,1] -> [10,10]`,
  `x != 0`, `¬(min = 10 ∧ x = -1)`, assert `y == 10`).

**F4: `ble` completeness.** `leLo`/`leHi` now treat `some i32Min` as an
effective `-∞` and `some i32Max` as an effective `+∞`; without those cases
`[min, ...]`/`[..., max]` were rejected as bounds for unbounded intervals even
though no `I32` lies outside them. `exists_gamma`, `leLo_complete`,
`leHi_complete`, and `ble_complete` are proved. T8's statement now carries an
explicit `InvariantEntailsSafety` hypothesis, with the inclusion half supplied
by `ble_complete` and the safety half limited by the conservative `entails`
(recorded in `known-gaps.md`).

**Verification after F3/F4.** `lake build` green (29 jobs, no warnings); 21/21
test files pass; `Audit.lean` lists 43 trusted lemmas and every one depends only
on `[propext, Quot.sound]` or smaller; CI fails on `Classical.choice`/`sorryAx`.
F3 is committed as `bf01dbb`; F4 is committed separately. F5–F8 remain.

---

## 15. Post-review fix — F5 (2026-11-27)

v1's state encoding now has an optional `mem` map (`certificate-v1.md` §5.1).
Keys are decimal array numbers; an absent array is `top`; a present array is one
interval covering every in-bounds cell; an unknown array number or an inverted
interval is malformed; `bot` carries no `vars`/`mem`. The array length comes from
the program's declared table, not the certificate.

This closes the M2.7/v1 mismatch: the interval instance's `mem` component is
expressible on the wire, so read/len precision is not silently lost in the M4
decoder. The M4.2 decoder must enforce the rules; no decoder exists yet, so this
is a format decision plus tests for the decoder milestone. F6–F8 remain.

---

## 16. Post-review fix — F6 (2026-11-27)

The three transfer towers are reduced to one. The final path is the
support-restricted `evalExprAbsOn`/`assignAbsOn` with `GammaOn`; the unused
`Env`/`evalExpr`/`assign`/`evalExpr_sound`/`assign_sound` layer (M2.6) and the
`AbsSound`/`evalExprAbs`/`assignAbs`/`evalExprAbs_sound`/`assignAbs_sound` layer
(M2.7) are removed. `IntervalTransfer` keeps the checked endpoint arithmetic and
`add`/`sub` T4c; `IntervalArrays` keeps `Abs`, `lenInterval`, `idxWithin`, and
`idxWithin_sound`. `Tests/Transfer.lean` and `Tests/Arrays.lean` now exercise
the final `On` path, so the tests pin the code that ships rather than a staging
layer. `Audit.lean` and the README/THEOREMS file lists were updated; the audit is
still clean.

This removes roughly 250 lines from the trusted tree and eliminates the risk of
two transfer semantics drifting without a proof that they agree. F7–F8 remain.
