# CertCore — Interim Review at M1

| | |
|---|---|
| Reviewed | 2026-11-24 |
| Milestone | **M1 — Semantics core** |
| Branch / commit | `feat/ast` @ `0f9505e` (`M1.11: pin Imp syntax and add the three example programs`) |
| Build | `lake build` green (21 jobs) |
| Tests | 8/8 green: `I32`, `Syntax`, `State`, `Eval`, `Step`, `Run`, `Edges`, `Examples` |
| `sorry` | none in `lean/` |
| Axioms (T1/T2, sampled) | `[propext, Quot.sound]` — manual `#print axioms`; `Audit.lean` does not check them yet |
| Verdict | **M1 is code-complete but not merge-ready.** One trusted-compiler correctness bug (F1) and one public-API namespace bug (F3) must be fixed before M2/M3. |

> **Update 2026-11-25:** F1–F4 are fixed and F7 is partly fixed; F5 is M2
> interface work. See §11. The findings below are the review as written, kept
> for the record.

This review is based on reading every Lean source, test, and design document; building the tree; running the eight test files; grepping for `sorry`; and printing the axiom footprint of the M1 theorems. The most important result is not the summary — it is **F1**, a reproducible bug in `Cmd.maxPoint` that silently truncates the CFG for any program whose largest point is inside an `if` or `while` body. The existing examples pass only because each has a later top-level point that accidentally sizes the array correctly.

---

## 0. Executive summary

- **The semantic spine exists and is coherent.** `I32` defines machine arithmetic with observable overflow; `eval` defines the four hazards as `none`; `compile` lowers the structured AST to a flat CFG; `step`/`run`/`Safe` define a deterministic, fuel-indexed operational semantics; `edges` is the checker-facing projection. This is the right shape for T5.
- **The proof content is deliberately thin.** T1 and T2 are short because the semantics is a function and `Safe` is *defined* as the finite-prefix property. That is the intended design (`D6`), not a shortcut: it moves the induction into `eval_det` and deterministic compilation, and it keeps every later proof an ordinary induction on the step count.
- **The milestone's exit criteria are too weak.** "Build green, T1/T2 closed, three examples evaluate correctly" is satisfied, but it did not catch F1. The examples are biased: every compiled test program has its maximum point outside the branch/loop body, so a too-small instruction array is masked.
- **The remaining risks are interface risks, not proof risks.** Compiled-CFG well-formedness, the `step → edge` bridge, and the `EdgeCmd`/`transfer`/`entails` interface are cheap to close now and expensive to discover inside T5. They are the natural exit work for M1.
- **The design decisions are defensible.** The edge machine, fuel-indexed `Safe`, `Int`-backed `I32`, division in `Expr`, total `State`, and derived entry point all buy something specific for T5 and the TCB. The one decision worth revisiting before M2 is strict `and`/`or`, because it changes which programs the language can certify.

---

## 1. M1 against its contract

Roadmap M1 (`docs/certcore-roadmap.md` §6) asks for eleven subtasks. Their state:

| ID | Subtask | Status | Evidence / deviation |
|---|---|---|---|
| M1.1 | `I32` with wrap | **done** | Checked ops return `Option`; wrap model; agreement lemma `ofIntWrap_agrees`; 20+ `#guard`/`#guard_msgs` checks. |
| M1.2 | `Expr` | **done** | Constants, variables, `+ - * /`, array read, length. |
| M1.3 | `Cmd` + `Program` | **done, with a deviation** | All formers plus `BExp`/`CmpOp`; points embedded. `div` is in `Expr`, not `Cmd` (see §6.4); roadmap still says `div` is a command. |
| M1.4 | `State` | **done** | Total `env`/`mem`; `init`; pointwise update lemmas; no `State.ext` yet. |
| M1.5 | `eval` | **done** | Four hazards as `none`; truncating division; strict `and`/`or`; tests pin both choices. |
| M1.6 | `step` | **done, but defective** | `compile`/`CFG`/`step` exist; **F1** shows `maxPoint` ignores branch/loop bodies, so some programs compile to a truncated machine. |
| M1.7 | `run` + `Safe` | **done** | Fuel exhaustion is not failure; halt stutter; `Program.safe` defined (misnamespaced, **F3**). |
| M1.8 | CFG `edges` | **done** | `EdgeCmd`/`Edge`/`edgesAt`/`edges`; ascending order; membership lemmas. |
| M1.9 | T1 `step_det` | **proved** | Statement narrowed to configuration determinism; the planned induction is in `eval_det` + compilation. Documented in `THEOREMS.md`. |
| M1.10 | T2 `safe_iff` | **proved** | `Safe ↔ ¬∃n, run n = none`; plus `safe_iff_exists` and `safe_iff_isSome`. Documented. |
| M1.11 | Three examples | **done as fixtures, not parsed** | `.imp` files + hand encodings in `Tests/Examples.lean`; no parser exists yet, so the `.imp` text itself is not executed or checked against the encoding. |

**Exit criteria:** build green (yes), T1/T2 closed (yes), three examples evaluate as expected (yes, via hand encodings). The criteria omit the two things that matter most at this boundary: a **compiler well-formedness** check and a **branch-tail** test. F1 is the result.

---

## 2. The tree at a glance

| File | Lines | Trust | Role | M1 state |
|---|---:|---|---|---|
| `lean/CertCore/I32.lean` | 282 | **yes** | Signed 32-bit values; checked and wrapping arithmetic | complete |
| `lean/CertCore/Semantics.lean` | 744 | **yes** | AST, state, `eval`, `compile`, `step`, `run`/`Safe`, `edges`, T1/T2 | complete except F1/F2/F4 |
| `lean/CertCore/Domain.lean` | 24 | yes | `CertDomain` interface sketch | **stub** (M2/M3) |
| `lean/CertCore/Cert.lean` | 21 | yes | Certificate type + total JSON decoder | **stub** (M4) |
| `lean/CertCore/Check.lean` | 21 | yes | Three obligation families + diagnostic | **stub** (M3) |
| `lean/CertCore/Proofs.lean` | 13 | yes | Theorem aggregator T1–T10 | **stub** (M3+) |
| `lean/CertCore/Audit.lean` | 18 | yes | `#print axioms` gate | **stub** (M3.8) |
| `lean/CertCore/Cli.lean` | 19 | yes | `certcore` executable | **stub** (M4.5) |
| `lean/Tests/*.lean` | 541 | no | Executable boundary tests (`#guard`, `#guard_msgs`) | complete for M1 |
| `examples/*.imp` | 15 | no | Three fixtures | complete as fixtures |
| `docs/*.md` | — | — | Plan, roadmap, theorem contract, TCB, format | partly stale (F8) |

Two consequences follow. First, the **only substantive trusted code at M1 is `I32` + `Semantics`**; the "kernel" (domain, certificate, checker) does not exist yet. That is normal for M1, but it means the M1 assurance is assurance about the *definitions*, not about any program's safety. Second, the test files are outside the library target: `lake build` does not run them, CI does. That is a reasonable split (tests are not part of the TCB), but it makes the CI list the real test registry, and the list is manual (F10).

---

## 3. What each part does, and why it matters to the whole

### 3.1 `I32` — the failure model

`I32` is an `Int` with a range proof. Two layers are kept separate:

- **Checked arithmetic** (`add?`, `sub?`, `mul?`, `neg?`, `div?`) returns `none` exactly when the mathematical result leaves `[-2^31, 2^31-1]` (or the divisor is zero / `min / -1`).
- **Wrap arithmetic** (`addWrap`, …) is the machine behaviour: reduce modulo `2^32` into the signed range.

`ofIntWrap_agrees` proves the two agree whenever the checked operation succeeds. This is the crucial lemma: it says the error model is a **refinement** of the machine, not a different machine. Without it, "overflow is a safety violation" would be a modelling assumption that could drift from the wrapping hardware.

**Contribution to the project.** This is where the safety property gets its arithmetic meaning. If overflow were impossible by construction (an unbounded `Int`) or silent (wrap only), the project would certify a different property. The checked/wrap split lets the concrete semantics treat overflow as a stuck state while still having a machine model to compare against. Downstream: `eval` turns `none` into a hazard; the interval domain must prove overflow freedom; `entails` at M2/M3 will consume the `isSome`/`none` lemmas. If `I32` is wrong, everything downstream is about the wrong arithmetic.

### 3.2 `Expr`, `BExp`, `Cmd`, `Program` — the AST

This is the structured source representation: constants, variables, arithmetic, array reads/lengths; comparisons and boolean connectives; `skip`/`assign`/`store`/`assert`/`if`/`while`/`seq`; and a `Program` carrying the constant length of every array. Atomic and branch commands carry their program point; `seq` is pure control; the entry point is derived (`Cmd.entry?`), not stored.

**Contribution.** It is the parser target, the Haskell mirror's JSON source (at M5), and the single place where program points are assigned. Points are not cosmetic: the certificate's abstract states are keyed by them, and the checker's obligations are indexed by them. The AST also encodes the constructs that create hazards (`store`, `assert`, `div` inside expressions, array reads) and the array-length table that makes bounds decidable.

**Important subtlety.** The AST has **no independent operational semantics**. `Cmd.compile` lowers it to a CFG, and `Program.safe` is defined over the compiled machine. So "the meaning of the source" is the *composition* of parsing and compilation; the compiler is trusted (see §6.1). This is a deliberate choice, and it is why F1 is a serious bug: a compiler defect changes the language, not merely an optimisation.

### 3.3 `State` — the total configuration

A state is a total environment `Var → I32` and a total memory `Arr → Array I32`. `init` zero-fills variables and allocates each declared array at its constant length; an undeclared array number reads as the empty array. The pointwise update lemmas (`get_set_same`, `set_set_noteq`, `memAt_setMem_*`, `get_init`, `memAt_init`) are the workhorses for the later transfer-soundness proofs.

**Contribution.** Totality is what keeps `eval` from getting stuck on a missing variable: a language-level hazard is `none`, a lookup is never a hazard. That separation is exactly what lets the checker's safety obligations be *structural* (division, array access, assert) rather than "well-formedness of the environment". It also gives T5 its base case: `State.init p` satisfies the initial invariant by `get_init`/`memAt_init`.

**Cost.** A typo in a variable name reads as zero rather than failing. The frontend must reject unbound names; the semantics stays total regardless. That is the right trade for proofs, but it puts weight on the frontend’s well-formedness checks (F7).

### 3.4 `eval` / `evalB` — the definition of safety

`eval : Expr → State → Option I32` returns `none` for:

1. signed overflow in `add`/`sub`/`mul`;
2. division by zero or `min / -1`;
3. out-of-bounds array read;
4. (in principle) an array length beyond the machine range, excluded by constant bounds.

`evalB` evaluates conditions; a failing operand fails the whole condition. `and`/`or` are **strict**: both sides are evaluated.

**Contribution.** This is the heart of the project. Safety is not a separate document; it is the statement that `eval`/`exec` never return `none`. The checker's three obligation families are the complement of those `none` cases. Everything else in the trusted tree exists to make this definition executable, deterministic, and amenable to an induction.

`exec` extends the same idea to commands: assignment failure, store bounds, and `assert` false all yield `none`. Note the asymmetry: `assert` is a *command* that fails, while its proof obligation is a *safety* obligation at the same point. T5 will use the obligation to show the step cannot fail.

**Cost of strictness.** See §6.5. `x != 0 && 10 / x > 1` is genuinely unsafe under this semantics, even though a C programmer would call it safe. That is a language-design choice, and it needs to be visible in the docs and benchmarks.

### 3.5 `compile`, `CFG`, `step` — the operational machine

`Cmd.compile` flattens the AST into an instruction array indexed by point. Atomic commands become `Instr.atomic cmd next`; `if`/`while` become `Instr.branch b t e`; sequencing threads a continuation `k`; a `while` body continues back to the guard; the program appends a halt point holding `skip` to itself. `CFG.step` fetches the instruction at a point, executes it, and moves to the successor.

**Contribution.** This is the object the semantics is *about*. It removes the continuation stack from the proofs: there is no runtime control context, only a point and a state. It makes one step one instruction, which is what makes `run` a simple `Nat` recursion and T5 an induction on step count. It also gives `edges` something concrete to project.

**Cost.** The compiler is in the TCB, and it has no independent correctness statement. F1 is the concrete risk; F2 (well-formedness) is the missing theorem that would contain it. `step` also returns `none` for an out-of-range point, conflating "malformed CFG" with "language hazard" (F7). Because the frontend is trusted and assigns dense points, that case should be unreachable; but "should be" is not a proof.

### 3.6 `run` / `Safe` — the property

`run cfg n p s` iterates `step` `n` times; `run 0` returns the starting configuration and `none` appears only when a step fails. `Safe cfg s := ∀ n, run cfg n cfg.entry s ≠ none`; `Program.safe p` specialises this to `Program.compile p` and `State.init p`.

**Contribution.** This is the plan’s `D6` choice realised. Infinite loops and the halt stutter are safe because every finite prefix is; divergence is not a safety violation. There is no coinduction and no termination side condition, so T2 is an ordinary equivalence and later proofs induct on `n`. `safe_iff_exists` is the form T5 will use: if every fuel count yields a configuration, the run never fails.

**Cost.** `Safe` is a safety property, not liveness. It says nothing about termination, and it cannot express "eventually". That is the right scope (`NONGOALS.md`), but it should be stated in the write-up so nobody reads `Safe` as total correctness.

### 3.7 `edges` — the checker's view

`Instr.edgesAt p` emits one edge for an atomic instruction and two for a branch (`assume b true`, `assume b false`). `CFG.edges` enumerates every point in ascending order and flat-maps `edgesAt`. `Edge` is `(src, EdgeCmd, dst)`; `EdgeCmd` is either `atomic cmd` or `assume b positive`. The membership lemmas (`mem_edges_atomic`, `mem_edges_branch_true`, `mem_edges_branch_false`) connect an instruction at `p` to the edge list.

**Contribution.** Edges are the **index set of the checker's obligations**. They are recomputed from the AST/CFG, never supplied by the certificate, so a hostile certificate cannot invent control flow. Branch guards become `assume` edges, which is where the domain's guard refinement will attach. This is the bridge between the operational semantics (`step` chooses one branch) and the static proof (`check` must discharge both branches).

**Cost.** Edges are a projection, not a semantics. There is no `EdgeCmd` execution function and no packaged theorem that a successful `step` corresponds to one edge in `cfg.edges` (F4). The ingredients are present — `step` unfolds to `instrAt`, and the membership lemmas produce the edge — but the bridge is not written. T5 will need it, especially for branch polarity.

### 3.8 Tests, CI, examples — the executable boundary

The eight test files are `#guard` programs: a false expectation fails elaboration, so it fails the build. They pin boundary values for `I32`, `entry?` for every command former, state updates, the four hazards, compile/step shapes, the exact edge list, and the three example outcomes. CI runs `lake build`, each test file, the `sorry` grep, and the audit script.

**Contribution.** The trusted definitions are not proved correct by these tests, but they are pinned against drift. The `#guard` style is the right low-dependency choice: no test framework, no Mathlib, one command per file. The `sorry` grep is a real gate; the audit script is currently a placeholder (F9).

**Weakness.** The tests are example-based and biased toward programs with a later top-level point. There is no test that every compiled target is in range, no branch-tail program, and no direct `maxPoint` test. That is exactly how F1 survived.

### 3.9 The stubs

`Domain`, `Cert`, `Check`, `Proofs`, `Audit`, and `Cli` are design documents in Lean syntax: they state the intended interfaces and the obligations, with no definitions yet. They are honest M0 placeholders and good signposts; they are not part of M1’s assurance. The `Domain` stub still describes `transfer` without fixing its input type; `Check` describes the edge obligation in terms of `transfer c (at p)`; the actual `c` will be an `EdgeCmd`, not a `Cmd` (F5).

---

## 4. Architecture and flow

### 4.1 The final runtime pipeline (plan §4.1, §10.1)

```
                       TRUSTED (Lean)                                   UNTRUSTED
 .imp ──parse(M4.5)──▶ Program ──compile(M1.6)──▶ CFG ──step/run(M1.6–1.7)──▶ Safe
                          │                        │
                          │                        └──edges(M1.8)──▶ List Edge
                          │                                              │
                          │                                              ▼
                          │                                   check(M3) ──▶ verdict
                          │                                        ▲
                          └──AST.json──▶ [Haskell M5] ──cert.json──▶ decode(M4)
                                             fixpoint/widening        (untrusted bytes)
```

The theorem that closes the loop is `check_sound : check p c = .ok → Program.safe p`. The certificate supplies abstract states only; the obligations are derived from the program and the edges. The Haskell side never contributes a verdict, only a proposal.

### 4.2 What M1 actually covers

```
 .imp text ──(no parser yet)──▶ [hand-written Program in tests]
                                   │
                                   ├──compile──▶ CFG ──step/run──▶ Option (Point × State)
                                   │              │
                                   │              └──edges──▶ List Edge
                                   └──(no AST JSON encoder yet)
```

M1 covers the **left half** of the pipeline: AST, compiler, CFG, semantics, edges. There is no parser, no certificate, no decoder, and no checker. The "kernel" is still a design. That is the correct state for M1, but it means the milestone’s value is that the *target* of T5 is now fixed and executable, not that any program has been verified.

### 4.3 How the parts will feed T5

T5 is an induction on `run n`. Each ingredient has an owner:

| T5 needs | Supplied by M1 | Still missing |
|---|---|---|
| Base case: `State.init p ∈ γ(entry)` | `State.init`, `get_init`, `memAt_init` | domain `top`/init and `top_sound` (M2/M3) |
| Every actual step matches an edge | `step`, `instrAt`, `mem_edges_*` | packaged `step → edge` lemma (F4) |
| Edge obligation transfers the invariant | `EdgeCmd`, `edges` | `transfer_sound` for `EdgeCmd`, including `assume` guards (M2/M3, F5) |
| The step cannot fail | `eval`/`exec` hazard cases, `assert` | `entails_sound` / safety-predicate test (M2/M3) |
| Every successor point is in range | `Cmd.compile` | **`compile_wf`** (F2); without it, a step can fail at the next `instrAt` despite all edge obligations |
| The run is a finite prefix | `run_succ`, `safe_iff_exists` | none |
| T1 determinism | `step_det`, `eval_det` | none |

This table is the real "interface" of M1. The top three rows are close; the fourth is the one that can silently break T5.

### 4.4 Trust boundary

**Trusted:** `I32`, `Semantics` (AST, compiler, `eval`, `step`, `run`, `Safe`, `edges`), and the future parser, decoder, checker, and `Audit`. **Untrusted:** the Haskell analyzer, the Python harness, and every certificate byte. A bug in the untrusted side yields a rejected certificate, not a wrong verdict; a bug in the trusted side changes what "safe" means. F1 is a trusted-side bug, which is why it dominates this review.

The tests are outside the TCB but inside the *assurance* story: they do not prove the definitions, they pin them. The audit is the only mechanism that proves the proof rests on nothing extra; at M1 it is empty (F9).

---

## 5. AST, CFG, and edges: three representations, three jobs

### 5.1 The difference in one table

| | **AST** (`Expr`, `BExp`, `Cmd`, `Program`) | **CFG** (`Instr`, `CFG`) | **Edges** (`EdgeCmd`, `Edge`) |
|---|---|---|---|
| Shape | Nested tree | Flat array indexed by point | List of `(src, cmd, dst)` triples |
| Control | Structural: `seq`, `ite`, `while` | Explicit successor per instruction; a branch has two targets | One edge per atomic instruction; two per branch |
| Point | Stored in each atomic/branch command | Implicit: the array index; targets are explicit | `src`/`dst` explicit |
| Guards | `BExp` inside `ite`/`while`/`assert` | `branch b t e` | `assume b true` / `assume b false` |
| Produced by | Parser (future) / tests | `Program.compile` | `CFG.edges` |
| Consumed by | Compiler, Haskell mirror | `step`, `run`, `Safe` | Checker obligations |
| Operational semantics | None directly | **Yes**: `step` | None; it is an obligation index |
| What it loses | Successors | Source nesting and point fields | Determinism (two outgoing edges per branch) and instruction grouping |
| Why it exists | Parse, mirror, assign points | Run and prove | Check and quantify |

### 5.2 The same program in three views

The running example from `Tests/Edges.lean`:

```
0: x := 0
1: while (x < 2) { 2: x := x + 1 }
3: assert (x == 2)
halt 4
```

**AST**:

```lean
.seq (.assign 0 "x" (.const 0))
  (.seq (.while 1 (.cmp .lt (.var "x") (.const 2))
                (.assign 2 "x" (.add (.var "x") (.const 1))))
        (.assert 3 (.cmp .eq (.var "x") (.const 2))))
```

**CFG**:

```
0: atomic (x := 0)         -> 1
1: branch (x < 2)          -> 2 (true), 3 (false)
2: atomic (x := x + 1)     -> 1
3: atomic (assert x == 2)  -> 4
4: atomic skip             -> 4        (halt stutter)
```

**Edges**:

```
(0, atomic x := 0,       1)
(1, assume x < 2 true,   2)
(1, assume x < 2 false,  3)
(2, atomic x := x + 1,   1)
(3, atomic assert x == 2, 4)
(4, atomic skip,         4)
```

The AST says *what the source said*; the CFG says *what one step does*; the edges say *what the certificate must prove*. The three views are a pipeline, not alternatives.

### 5.3 Why not one representation?

- **Only AST.** T5 would induct over nested commands and need a control stack or a simulation relation; the checker would have to derive successors from the structure. That is exactly the proof work the edge machine was chosen to avoid (§6.1).
- **Only CFG.** The parser would emit a CFG directly, losing the compositional syntax and the structured AST that the Haskell mirror reads. Point assignment and `entry?` would move into the parser; the compiler would disappear, but so would the clean separation between "what the source says" and "how it runs".
- **Only edges.** Two outgoing edges at a branch make the semantics look nondeterministic; `step` would need a relational formulation and T1 would need a determinism proof. The CFG keeps one instruction per point and chooses at runtime; the edges keep the static case split. That is the right division.
- **All three, but with two trusted bridges.** `compile` (AST → CFG) and `edges` (CFG → edges) are the only bridges. `compile` is trusted; `edges` is derived from trusted data, so it adds no trust. The design is sound as long as the bridges are well-formed — which is F2/F4.

### 5.4 The `atomic` cluster

The word "atomic" appears at four distinct types. They are not redundant; each layer knows exactly what the next layer needs.

| Name | Type | Carries point? | Carries successor? | Carries guard? | Meaning | Produced by | Consumed by |
|---|---|---|---|---|---|---|---|
| `Cmd.skip p`, `Cmd.assign p x e`, `Cmd.store p a i v`, `Cmd.assert p b` | `Cmd` | **yes** (`p`) | no (structure decides) | no | Source statement with its point | Parser / tests | `Cmd.compile`, `entry?`, `maxPoint` |
| `AtomicCmd.skip`, `.assign x e`, `.store a i v`, `.assert b` | `AtomicCmd` | no | no | no | Point-free **effect** of an atomic action | `Cmd.compile` (inside `Instr.atomic`) | `CFG.exec`, `EdgeCmd.atomic` |
| `Instr.atomic cmd next` | `Instr` | implicit (array index) | **yes** (`next`) | no | One CFG row: do `cmd`, go to `next` | `Cmd.compile` | `CFG.step`, `Instr.edgesAt` |
| `EdgeCmd.atomic cmd` | `EdgeCmd` | no (`Edge.src`) | no (`Edge.dst`) | no | The command on a checker edge | `Instr.edgesAt` | `CFG.edges`, future `transfer`/obligations |
| `Edge { src, cmd, dst }` | `Edge` | **yes** (`src`) | **yes** (`dst`) | via `cmd` | One obligation unit | `edgesAt` / `edges` | Checker |
| `Instr.branch b t e` | `Instr` | implicit | **yes** (two) | **yes** (the test) | Control decision | `Cmd.compile` | `CFG.step` |
| `EdgeCmd.assume b positive` | `EdgeCmd` | no | no | **yes** | One branch outcome on an edge | `Instr.edgesAt` | Checker transfer/refinement |
| `Cmd.ite p b t e`, `Cmd.while p b body` | `Cmd` | **yes** (`p`) | no | **yes** | Source control structure with subcommands | Parser | `Cmd.compile` |
| `Instr.atomic .skip halt` | `Instr` | halt index | halt | no | Halt stutter | `Program.compile` | `step` |

The four "atomic" senses, in order:

1. **Source atomic command** (`Cmd.assign p …`): syntactic, carries the point, no successor. `compile` needs the point and the effect.
2. **Compiled atomic action** (`AtomicCmd.assign …`): only the effect, no point or successor. `exec` needs nothing else.
3. **CFG atomic instruction** (`Instr.atomic … next`): effect + successor. `step` needs both.
4. **Checker atomic edge command** (`EdgeCmd.atomic …`): effect as an edge label; the successor is in `Edge.dst`, the source in `Edge.src`. The checker needs both, but not the other branch.

This is **phase separation / information hiding**, not duplication. The risk is naming: a newcomer sees `skip`/`assign`/`store`/`assert`/`atomic` at four types and can confuse them. The doc comments are already good; a short glossary in `docs/` would help. The only bridge between the layers is `Cmd.compile`, which is trusted.

The branch case is the most instructive:

- `Cmd.ite` has subcommands; `Instr.branch` has only target points. The subcommands are compiled elsewhere; the branch instruction does not contain them.
- `step` at a branch chooses `t` or `e` from `evalB`; `edges` lists *both* `assume` edges. The CFG is deterministic; the edge view is not. T5 must relate them (F4): if `evalB` is true, the taken edge is the `assume true` edge.
- `Cmd.while` compiles to a branch with the body entry and the continuation, plus a back edge from the body to the guard. The loop is not a special instruction; it is a branch and a cycle in the CFG.

### 5.5 Other overloaded names

| Name cluster | Members | What differs |
|---|---|---|
| Safety | `CFG.Safe`, `Program.safe`, `safe_step`, `not_safe_of_step_none`, `safe_iff`, `safe_iff_isSome`, `safe_iff_exists` | `Safe` is the definition (`∀ n, run n ≠ none`); `Program.safe` specialises to `compile` + `init` (currently misnamespaced, F3); the rest are introduction/elimination forms. `safe_step` says a safe configuration’s first step is `some`; `not_safe_of_step_none` is its contrapositive; `safe_iff` is "no failing prefix"; `safe_iff_isSome` is the `isSome` form; `safe_iff_exists` is the finite-prefix form T5 will use. |
| Step | `CFG.exec`, `CFG.step`, `CFG.run` | `exec` is one atomic effect (`State → Option State`); `step` adds instruction fetch, control, and returns `(Point × State)`; `run` iterates `step`. |
| Compile | `Cmd.compile`, `Program.compile` | `Cmd.compile` takes a continuation point and an instruction array; `Program.compile` allocates the array, chooses the halt point, and delegates. |
| Entry | `Cmd.entry?`, `Program.entry?` | Both are derived; `Program.entry?` delegates to the body. In practice both are always `some`, because every `Cmd` constructor has a point — the `Option` is a type-level hedge that forces `getD halt` in `compile` (F7). |
| Edges | `Instr.edgesAt`, `CFG.edges`, `Edge`, `EdgeCmd` | `edgesAt` is per instruction; `edges` is the whole graph; `Edge` is the triple; `EdgeCmd` is the command/guard label. |
| Evaluation | `eval`, `evalB`, `CFG.exec`, `I32.add?` etc. | `eval` is expressions to `Option I32`; `evalB` is conditions to `Option Bool`; `exec` is commands to `Option State`; `I32.*?` are the checked arithmetic primitives. |
| Points | `Point`, `Cmd.maxPoint`, `CFG.entry`, `halt`, `instrs.size` | `Point` is the type; `maxPoint` is the bound used to size the array (buggy, F1); `entry` is the start; `halt` is `maxPoint + 1`; `instrs.size` is `halt + 1`. These are not the same set, and the certificate format’s `|Points|` must be pinned to one of them (F5/F11). |

---

## 6. Decisions and alternatives

### 6.1 Edge-machine semantics via a trusted compiler (the biggest decision)

**Decision.** The AST is lowered by `Cmd.compile` to a flat CFG of one instruction per point; `step` walks one instruction at a time; branches are instructions with two targets; loops are cycles; halting is a self-loop.

**Why.** It makes T5 a one-page induction over steps, with no continuation stack in the proof state and no simulation lemma between two semantics. It aligns the operational step with the checker’s edge obligations: one step consumes one edge, so the induction case is "the edge obligation gives the successor invariant". It also makes T1 immediate, because `step` is a function.

**Alternatives.**

- **Structural small-step on `Cmd` with control frames.** No compiler in the TCB, and T1 would be a real induction on commands and `eval`. But T5 would have to reason about a runtime stack and about which command is "next"; the edge projection would need a simulation lemma. That is more proof work in the load-bearing theorem, which is exactly what the project is trying to avoid.
- **Big-step semantics.** Natural for terminating programs, but it has no place for divergence and no step count; `Safe` would need a coinductive or separate divergence predicate. Rejected under `D6`.
- **Direct CFG as parser output.** Simpler pipeline, but loses the structured AST and the Haskell mirror; point assignment moves into the parser; `entry?`/`maxPoint` disappear. The AST is also the natural place to enforce source-level invariants (arrays, points).
- **Definitional interpreter on the AST.** Similar to structural small-step; no edges; the checker would need to derive obligations from syntax. More work at M3.

**Cost accepted.** The compiler is trusted and unverified. There is no formal source semantics in the tree, so a compiler-correctness theorem would have nothing to relate the CFG to: the CFG *is* the meaning. This is acceptable only if the compiler is small, tested, and well-formed. F1 shows it is small but not yet correct; F2 is the missing well-formedness theorem. A future compiler-correctness theorem (structural semantics + simulation) would shrink the trust, but it is a second project and not on the critical path.

**Verdict.** Right for the month, provided F1/F2 are fixed before T5.

### 6.2 Fuel-indexed `Safe` (D6)

**Decision.** `Safe cfg s := ∀ n, run cfg n cfg.entry s ≠ none`; fuel exhaustion is not failure; divergence is safe.

**Why.** No coinduction, no termination side conditions, no `while`-termination proof. T2 becomes an ordinary equivalence, and every later proof inducts on the step count. It is honest: the language certifies safety properties, not liveness.

**Alternatives.** Coinductive `Safe` (needs guardedness and coinduction, and interacts badly with the step function); relational semantics (more faithful to the literature, but a week of proof plumbing); step-indexed logical relations (overkill for a toy language).

**Cost.** `Safe` cannot express termination; a diverging loop is safe. That is the intended scope (`NONGOALS.md`), but it must be stated in the paper. The halt stutter means `run 100` on a terminated program stays at halt; tests pin this.

**Verdict.** Right. T2’s statement change is documented in `THEOREMS.md` and is not a hidden weakening.

### 6.3 `I32` as `Int` + proof, with checked/wrap split

**Decision.** `I32` is a structure `{ val : Int, min_le, le_max }`; checked ops return `Option`; wrap ops are total; `ofIntWrap_agrees` connects them.

**Why.** Overflow must be *observable*, not impossible by construction (roadmap M1.1). `Int` keeps the range proofs short and lets `omega` do the work. The wrap model is the machine; the checked model is the error semantics; the agreement lemma prevents drift. `UInt32`/`BitVec` would force bit-level reasoning in every interval proof and add a library dependency.

**Alternatives.** `UInt32` with `BitVec` (faithful to the machine, but heavier proofs and a less familiar arithmetic for intervals); unbounded `Int` (overflow disappears, so the safety property becomes wrong); wrap-only `Int32` (overflow is silent, so the checker cannot certify "no overflow").

**Cost.** The Lean value is not the runtime representation; the checker never executes the program, so this is a proof-level model, not a performance model. `OfNat I32` wraps, which is a footgun in specifications (a numeral beyond range silently wraps; `ofInt?` is the checked constructor). The tests use `ofIntWrap` deliberately, but a future spec could write `(2147483648 : I32)` and get `-2147483648`. Recommend a lint/review rule: source literals use `ofInt?`, tests use `ofIntWrap`, and no `OfNat` in trusted definitions.

**Verdict.** Right. The split is the project’s clearest modelling win.

### 6.4 Division in `Expr`, not `Cmd`

**Decision.** `Expr.div` is an expression former; there is no `Cmd.div`. `eval` returns `none` on zero and `min / -1`; division truncates toward zero (`Int.tdiv`).

**Why.** One encoding of `x := a / b`. A separate `div` command would duplicate the assignment form and give the AST two ways to say the same program, which complicates the parser, the mirror, and point assignment. Failure modes belong in `eval`, where every partial operation already lives. `Int.tdiv` matches C/x86 `idiv`; Lean’s Euclidean `/` does not.

**Alternatives.** `Cmd.div` (roadmap wording; more syntax, duplicate semantics); a partial expression with a proof of definedness (more type-level machinery, and the checker still needs a safety obligation); `assert b ≠ 0; x := a / b` (the user can write this, but it changes the program and the point structure).

**Cost.** The roadmap still says `div` is a command; that is documentation drift (F8). There is no remainder, no standalone division statement, and no way to express a trapping division without an assignment. The last point is minor for a toy language.

**Verdict.** Right; amend the roadmap rather than adding a command.

### 6.5 Strict `and` / `or`

**Decision.** `BExp.and`/`or` evaluate both operands; a failing operand fails the condition.

**Why.** It keeps every safety obligation **unconditional at a point**. If `and` short-circuited, a partial operation on the right would be safe only when the left is true; the checker would need a *conditional* obligation ("if the left is true, then the right is defined"), which the per-point `ble`/`entails` interface does not express. A short-circuit language would therefore need path predicates or a richer obligation language — exactly the complexity the project is trying to avoid.

**Alternatives.** C-style short-circuit (more familiar, but conditional obligations); a three-valued logic (more precise, but a new semantics and a new checker rule); restricting partial operations to statements (a language restriction, not a semantics choice).

**Cost.** The language rejects guard-protected division inside conditions. For example, `if (x != 0 && 10 / x > 1) { ... }` is safe in C for `x = 0`, but in Imp `evalB` evaluates `10 / x` and fails. The statement-level idiom `if (x != 0) { y := 10 / x; }` works, because the `assume x != 0 true` edge refines the state at the body point. If the benchmark suite (M10) expects C-like guards, this will show up as false negatives; the language, not the checker, is the cause.

**Verdict.** Defensible, and the rationale is documented in the module header. But it should be a **documented limitation** in `known-gaps.md`/the paper, and the M10 benchmark suite should use the statement-level idiom. Revisit only if the experiment needs conditional guards; changing the semantics after M2 is expensive.

### 6.6 Total `State`

**Decision.** `env : Var → I32` and `mem : Arr → Array I32` are total; `init` is zero/empty; unbound variables read zero, undeclared arrays read empty.

**Why.** `eval` never gets stuck on a lookup. The only `none` cases are the four language hazards, which is exactly what the checker’s obligations are about. A partial map would add "unbound" as a fifth failure mode and force every proof to carry a well-formedness hypothesis.

**Alternatives.** Partial maps (`Var → Option I32`) with `none` for unbound (more faithful, more cases); a well-formedness precondition on `Program` (more precise, but the semantics would no longer be total); a map with a default plus a proof of the default (same as total, more machinery).

**Cost.** A typo reads zero. The frontend must reject unbound names; the semantics does not. That puts weight on the parser’s checks and on `Program.WF` (F7). The certificate format also keys states by variable name, so a name mismatch is a decoder/diagnostic issue, not a semantics issue.

**Verdict.** Right for proofs; pair it with a real frontend well-formedness check.

### 6.7 Points in the AST and a derived entry

**Decision.** Every atomic/branch command carries a `Point`; `seq` does not; `entry?` is derived from the body; `maxPoint` sizes the array; the halt point is `maxPoint + 1`.

**Why.** Points are the certificate’s keys and the checker’s obligation indices. Storing them in the AST avoids a side table that could disagree with the program. Deriving `entry?` prevents a `Program` from disagreeing with itself about where it starts. The frontend assigns points in source pre-order, so the numbering is deterministic and the Haskell mirror can reproduce it.

**Alternatives.** A point-free AST plus a separate labelling map (more flexible, but two sources of truth); a CFG as parser output (fewer layers, but loses the AST); de Bruijn indices (compact, but unreadable in certificates and diagnostics).

**Cost.** AST equality includes points, so two syntactically identical commands at different points are different values (the `Syntax` test pins this). Duplicate or non-dense points are representable; `place` silently ignores out-of-range writes and `CFG` slots default to halt self-loops. That is F1’s neighbourhood and the reason `Program.WF` is needed. `entry?` is always `some`, but typed `Option`, forcing `getD halt` in `compile` (F7).

**Verdict.** Right; make well-formedness explicit and make `entry` total.

### 6.8 Halting as a stutter

**Decision.** Compilation appends a halt point `maxPoint + 1` holding `skip` to itself; `step` at halt returns `(halt, s)`; `none` is reserved for hazards (and out-of-range points).

**Why.** `run` is total and needs no third "halted" case. Termination is not an error; `Safe` treats it as a stutter. The checker gets a trivial halt edge.

**Alternatives.** A halted configuration constructor (`run` returns `Option (Option (Point × State))` or a sum type); `none` for halt (would make every terminating program unsafe); a separate `run` result type. All add cases to every proof and to `Safe`.

**Cost.** The halt point is in the instruction array and in `edges`; `run 100` on a terminated program stays at halt; the point space includes one extra point. Tests must expect the stutter. The certificate format’s `|Points|` must decide whether halt is a point (F5/F11).

**Verdict.** Right. The simplicity is worth the extra edge.

### 6.9 Edges are recomputed, never certificate-supplied

**Decision.** `CFG.edges` derives the edge list from the compiled CFG; the certificate carries states only. Branch labels are recomputed by the trusted semantics.

**Why.** A hostile certificate cannot invent control flow. The checker’s obligations are structural, so a missing state defaults to `⊤` and is still sound. Certificate size measures only the invariant, which is what the experiment (C4) wants. The plan’s sketch had `successors` and `assertions`; both are deliberately dropped (`certificate-v1.md` §10).

**Alternatives.** Certificate-supplied successor sets (supports coarsened partitions and analyzer-chosen sparse graphs, but lets the certificate influence the obligation set); per-assertion states (convenient, but duplicates the sparse map and distorts byte counts); a certificate-supplied CFG (would move the program’s meaning into untrusted bytes — unacceptable).

**Cost.** Coarsened label partitions are out of v1; the analyzer must use the trusted label update. This is documented as an open item, and it is the right v1 trade.

**Verdict.** Right.

### 6.10 One branch = one step, two edges

**Decision.** A branch is a single `Instr.branch`; `step` evaluates the guard and chooses a side in one step; `edges` emits both `assume` edges.

**Why.** The step relation stays deterministic (T1 immediate), and the checker sees both possible outcomes (so it must discharge both). The guard refinement attaches to the `assume` edge, which is the natural place for the domain’s transfer.

**Alternatives.** Two step rules (`branch-true`, `branch-false`) would make `step` relational and T1 a determinism proof; two instructions (one per outcome) would duplicate the guard evaluation and complicate `run`; edge-level semantics would lose the instruction fetch.

**Cost.** T5 must select the taken edge based on `evalB`; that is the `step → edge` bridge (F4). The untaken edge’s obligation is checked but vacuous for this trace, which is correct but means the certificate must still satisfy it.

**Verdict.** Right; add the bridge lemma.

### 6.11 Smaller decisions

| Decision | Why | Alternative | Cost |
|---|---|---|---|
| No Mathlib; local `funUpdate` and lemmas | `D2`: small TCB, fast build, one language | Mathlib (`Function.update`, list lemmas) | Reimplement a few lemmas; they are trusted and must be reviewed |
| JSON certificates (`D4`) | Human-readable; LLM/tool-friendly; verbosity is the measured cost | S-expressions, Protobuf, CBOR | Larger bytes; decoder must be total |
| Haskell analyzer (`D3`) | Architectural trust boundary; good for fixpoints | Lean/Python/OCaml | Two implementations to keep in sync; JSON plumbing |
| Python harness (`D9`) | Fast to write; no code sharing with the analyzer | Haskell/shell | Another language in the repo; not in the TCB |
| Tests as `#guard` + per-file CI | No dependencies; failure is a build failure | Lean test framework, Python runner | Manual CI list; no aggregate; `Tests/Run.lean` is a test, not a runner |
| `ble : Bool` + `ble_sound` (`D7`) | Predictable compiled cost; explicit reflection | `Decidable` everywhere | More lemmas; the checker must call `ble` |
| `#print axioms` as a gate (`D10`) | Catches `sorry`/`Classical.choice` | Trust the proof | Must be wired into CI (not yet) |

---

## 7. Findings

### F1 — **Critical**: `Cmd.maxPoint` ignores `if`/`while` bodies, truncating the CFG

`Cmd.maxPoint` (`Semantics.lean:478`) returns only the branch point for `ite` and `while`:

```lean
| .ite p _ _ _ => p
| .while p _ _ => p
```

The subcommands can contain higher-numbered points. `Program.compile` sizes the instruction array as `maxPoint + 2`, and `place` silently ignores writes at `p ≥ size` (`Semantics.lean:490`). The result is a CFG whose branch target is outside the array: `step` jumps to a point with no instruction, and the next `step` returns `none`.

**Minimal reproduction** (verified with `lake env lean`):

```lean
def loopTail : Program :=
  { body := .while 0 (.cmp .lt (.const 0) (.const 1))
              (.assign 5 "x" (.const 1)), arrays := #[] }

#eval (Program.compile loopTail).instrs.size          -- 2   (expected 7)
#eval (Program.compile loopTail).edges.map (fun e => (e.src, e.dst))
-- [(0, 5), (0, 1), (1, 1)]  -- target 5 has no instruction
#eval (step (Program.compile loopTail) 0 (State.init loopTail)).map (fun r => r.1)
-- some 5
#eval (step (Program.compile loopTail) 5 (State.init loopTail)).map (fun r => r.1)
-- none
```

`ifTail` behaves the same way: `size = 2`, edges to 5 and 6, no instructions at 5/6. The body is compiled at 5/6 but `place` drops it.

**Why the tests miss it.** Every compiled test program has a later top-level point that raises `maxPoint` above the body points:

- `Tests/Step.lean` sample: loop body point 2, then `assert` at 3, so `maxPoint = 3`; the body at 2 is in range.
- `Tests/Examples.lean` `safe.imp`: loop body point 3, then `assert` at 4; in range.
- The straight-line examples have no branches.

A program that *ends* in a loop or an `if` — the common case in a benchmark suite — is broken.

**Fix** (two lines):

```lean
| .ite p _ t e => max p (max t.maxPoint e.maxPoint)
| .while p _ body => max p body.maxPoint
```

**Regression tests** (add to `Tests/Step.lean` or a new `Tests/Compile.lean`):

```lean
def b : BExp := .cmp .lt (.const 0) (.const 1)
#guard Cmd.maxPoint (.while 0 b (.skip 5)) = 5
#guard Cmd.maxPoint (.ite 0 b (.skip 5) (.skip 6)) = 6
-- and, for every compiled test program:
#guard cfg.edges.all (fun e => e.dst < cfg.instrs.size)
```

This is a trusted-compiler bug: it changes the program’s meaning silently. It must be fixed before M2/M3.

### F2 — **High**: no compiled-CFG well-formedness theorem

Even with F1 fixed, T5 needs a hypothesis that every successor point is inside the instruction array. Otherwise a `step` can succeed to an out-of-range point, and the *next* `step` fails; all edge obligations could still hold, because the certificate cannot influence the CFG’s targets. The compiled CFGs are well-formed by construction, but that is not proved.

**Needed:** a point set/`maxPoint` bound, a `place`-in-range lemma, and a `CFG.WF` predicate, roughly:

```lean
def CFG.WF (cfg : CFG) : Prop :=
  cfg.entry < cfg.instrs.size ∧ ∀ e ∈ cfg.edges, e.dst < cfg.instrs.size

theorem Program.compile_wf (p : Program) : (Program.compile p).WF
```

The proof needs `p ∈ c.points → p ≤ c.maxPoint`, `place` writing only inside the array, and the observation that every continuation/target is either a subcommand entry or the halt point. F1 is exactly a failure of the first lemma. Add a test that scans `cfg.edges` targets for every test program.

### F3 — **Medium**: `Program.safe` is namespaced `CFG.Program.safe`

At `Semantics.lean:591`, `def Program.safe` is declared inside `namespace CFG`, so its name is `CertCore.CFG.Program.safe`, not `CertCore.Program.safe`. Consequences:

```lean
#check CertCore.Program.safe        -- unknown identifier
example (p : Program) : Prop := p.safe
-- invalid field `safe`: the environment does not contain `CertCore.Program.safe`
```

The docs and the module header refer to `Program.safe`, and dot notation — the natural way to use it — fails. No test uses it, so the build is green. T5’s statement will want `Program.safe`, so fix it before M3.

**Fix:** move the definition outside `namespace CFG` (after `end CFG`) and declare it in `namespace Program`:

```lean
namespace Program
def safe (p : Program) : Prop := CFG.Safe (Program.compile p) (State.init p)
end Program
```

### F4 — **Medium**: no `step → edge` bridge

`step` and `edges` are two views of the same machine, but there is no theorem that a successful step corresponds to an edge in `cfg.edges` with matching source, destination, command, and guard polarity. The ingredients exist:

- `step` unfolds to `cfg.instrAt p` and then `exec` or `evalB`;
- `mem_edges_atomic`, `mem_edges_branch_true`, `mem_edges_branch_false` put the relevant edge in `cfg.edges`.

T5 can case on the instruction and on `evalB` and use these lemmas directly, so this is not a blocker in principle. But packaging it now de-risks M3 and gives the edge view an executable meaning:

```lean
theorem step_edge {cfg : CFG} {p : Point} {s : State} {q : Point} {s' : State}
    (h : step cfg p s = some (q, s')) :
    ∃ e ∈ cfg.edges,
      e.src = p ∧ e.dst = q ∧
      (match e.cmd with
       | .atomic cmd => exec cmd s = some s'
       | .assume b true  => evalB b s = some true  ∧ s' = s
       | .assume b false => evalB b s = some false ∧ s' = s)
```

The `assume` cases are the branch-polarity link; the `atomic` case is the effect link. This is also the natural place to define an `EdgeCmd` execution relation for `transfer_sound` (F5).

### F5 — **Medium**: the M2/M3 interface drifted from the plan

M1 introduced `EdgeCmd`, but the `CertDomain` sketch in the plan (`§4.2`) and `Domain.lean` still describe `transfer : Cmd → Abs → Abs`. The checker’s edge obligation is over `EdgeCmd` (`Check.lean:10`, `certificate-v1.md` §8), and `Cmd` has no `assume` case. M2 must settle:

1. **`transfer` input.** `transfer : EdgeCmd → Abs → Abs`, or a separate `guardRefine : BExp → Bool → Abs → Abs` plus `atomicTransfer`. The soundness statement must be against an edge semantics (F4), not `Cmd`.
2. **Safety entailment.** `ble` cannot express `x ≠ 0` as a single interval target (`certificate-v1.md` §12.6). M2/M3 need `entails : Abs → BExp → Bool` (a three-valued abstract evaluation) with its own soundness theorem against `evalB`, and T5 gains one hypothesis. This is not in the plan’s `CertDomain` structure; it should be added before the interval instance.
3. **Point space.** The certificate format says `point ∈ [0, |Points|)` where `|Points|` is “the number of program points in the AST” (`certificate-v1.md` §3.1). The implementation’s array size is `maxPoint + 2` including the halt point. If points are not dense, `|Points|` and `instrs.size` differ. Pin the definition (recommend: `|Points| = instrs.size`, halt included; the frontend guarantees dense unique points and the decoder uses the same bound).
4. **Unreachable hazard points.** Missing states default to `⊤`; a safety obligation at an unreachable division/assert with `⊤` will fail. The analyzer must emit `bot` at unreachable hazard points, not omit them. `certificate-v1.md` §7 says “a reachable state” but the issue is broader; clarify for M5.

Settling these before M2.6 is cheaper than discovering them inside `transfer_sound`.

### F6 — **Medium**: strict booleans limit the certifiable programs

This is a deliberate decision (§6.5), but it needs to be visible. The current semantics makes `if (x != 0 && 10 / x > 1) …` fail for `x = 0`; the checker cannot rescue it, because the concrete `evalB` fails. The statement-level idiom works. For the benchmark suite, this is a design constraint, not a checker weakness.

**Recommendation:** add a `known-gaps.md` entry (“no short-circuit conditions; guard-protected partial operations inside a condition are not expressible”), use the statement-level idiom in the examples, and decide before M10 whether to change the semantics. Changing to short-circuit after M2 would require conditional safety obligations and a new `entails` rule; that is a real cost, so decide now.

### F7 — **Medium**: the compiler is fail-open

Three places silently absorb malformed input:

- `Cmd.place` (`Semantics.lean:490`) drops writes at `p ≥ size`; this turned F1 into a truncated program instead of a build failure.
- `Program.compile` uses `entry?.getD halt` (`Semantics.lean:525`); `entry?` is always `some`, so the default hides an impossible case.
- `CFG.instrAt` uses `getD p (.atomic .skip p)` (`Semantics.lean:470`) after a `p < size` guard; the default is dead code.

In a TCB, fail-open is the wrong default: a bug should be a failed test or a stuck proof, not a smaller program. The best fix is to make the invariants explicit: `Cmd.entry : Point` (total), `Program.entry : Point`, `Program.WF` (dense unique points, arrays/vars in range, `maxPoint` bounded), and `compile_wf`. If a total signature is too invasive, at least add tests that assert every write is in range and every target is in range. Also bound `maxPoint` in the frontend: a hostile AST with a huge point would allocate a huge array in `Program.compile`.

### F8 — **Low, but fix before merge**: documentation drift

The tree is at M1, the docs still describe M0 in several places:

- `README.md:8` — “Status: **M0 — bootstrap** … No checker yet: M1–M4 build it” while the layout table says `Semantics.lean` has T1/T2 proved.
- `docs/known-gaps.md:12` — “none yet — the M0 tree contains no proofs and no `sorry`” while M1 has proofs and no `sorry`.
- `lean/CertCore/Semantics.lean:10` — “M1.11 examples pending” while `Tests/Examples.lean` exists; lines 39–42 have a “Pending” list that duplicates T1/T2/edges, contradicting the “complete” header.
- `docs/TCB.md:13` — lists a “Parser + CFG frontend” at M1, but there is no parser; the compiler exists, the parser is M4.5. The table also attributes `I32` to `Semantics.lean`; it is in `I32.lean`.
- `docs/certcore-roadmap.md:163` — M1.3 says `div` is a command; the code has `Expr.div`.
- The branch is `feat/ast` for all eleven subtasks, while the roadmap names `feat/ast` (M1.1–M1.3) and `feat/semantics` (M1.4–M1.11); `main` is still at M0. The M1 branch has not been merged, so CI on `main` does not exercise M1.

These are cheap fixes and they are part of the milestone’s contract: `THEOREMS.md` is the theorem ledger, and the README is the front door.

### F9 — **Low**: the audit is still a stub

`Audit.lean` contains no `#print axioms` commands, so CI does not check the axiom footprint of T1/T2 (or of any I32 lemma). A manual check gives `[propext, Quot.sound]` for `step_det`, `safe_iff`, `safe_iff_exists`, `ofIntWrap_agrees`, and `mem_edges_branch_true` — clean, but unverified by the gate. Add `#print axioms` for every proved theorem now; it is cheap and catches `sorryAx`/`Classical.choice` drift. `#print axioms` does not fail the build on unexpected output, so M11.4 still needs a comparison/gate.

### F10 — **Low**: test coverage is example-based and biased

The eight files are good, but the suite has no:

- branch-tail program (F1’s class);
- target-range assertion over `cfg.edges`;
- direct `maxPoint` test;
- nested `ite` inside `while`/`seq` compile test;
- duplicate-point or non-dense-point test (the documented last-write-wins behavior);
- aggregate runner (`Tests/Run.lean` is a test of `run`, not a runner — the name is confusing);
- test for `Program.safe` (F3).

Add a `Tests/Compile.lean` with a small table of shapes (straight line, if-tail, loop-tail, nested, duplicate points) and the target-range `#guard`. Consider `Tests/All.lean` importing every test file so CI has one command; the current manual list in `ci.yml` is easy to forget.

### F11 — **Low**: point-space and ⊤ details for M4/M5

Two follow-ons from F5 that are worth recording now:

- `|Points|` in the certificate format must match the implementation’s bound (F5.3).
- Missing states default to `⊤`; safety obligations at unreachable hazard points require explicit `bot`. The analyzer’s fixpoint should compute `bot` for unreachable points and emit it. The format supports `bot`; the docs should say why it is needed.

### F12 — **Low**: code polish

- `Cmd.entry?`/`Program.entry?` are always `some`; make them total (`entry : Point`) and remove `getD halt` (F7).
- `CFG` has no `DecidableEq`; tests project through `Option (Point × State)` instead. Deriving it is cheap and would simplify tests.
- `State` has no extensionality lemma; T5 may want `State.ext` (two states equal if `get`/`memAt` agree).
- `I32` has `OfNat` that wraps; see §6.3. Add a comment at every use site or remove the instance from the trusted namespace.
- `CFG.instrAt`’s default is dead; replace with a total lookup that cannot silently substitute a skip.
- `State.setMem` can change an array’s length; `exec.store` uses `Array.set`, which preserves it. A lemma `memAt_setMem_size` (when the new array has the same size) would pin the invariant that `len` is constant.
- `eval.len` returns `none` if the length exceeds `i32Max`; the frontend’s constant bounds exclude it, but that should be a stated invariant.

---

## 8. What M1 actually establishes

It is worth being precise about the assurance level, because “M1 reached” can sound like more than it is.

| Claim | Proved? | Where / note |
|---|---|---|
| Checked arithmetic is sound; wrap agrees when checked succeeds | **yes** | `I32.lean` lemmas; tested |
| `eval`/`evalB` are deterministic | **yes** | `eval_det`, `evalB_det` |
| `step` is deterministic | **yes** | T1 |
| `Safe` is equivalent to “no failing finite prefix” | **yes** | T2, `safe_iff_exists` |
| The compiled CFG is well-formed (targets in range) | **no** | F2; F1 is a counterexample to `maxPoint` |
| A successful step corresponds to an edge | **no** | F4 |
| The compiler preserves the source meaning | **not stated** | The CFG *is* the meaning; compiler is trusted |
| A domain is sound | **not started** | M2 |
| The checker is sound (T5) | **not started** | M3 |
| The decoder is total (T10) | **not started** | M4 |
| The parser exists | **not started** | M4.5 |

**No program has been proved safe at M1.** What M1 proves is that the safety question is well-posed: `none` is the failure, `Safe` is the finite-prefix property, and the machine is deterministic. That is the right thing to prove first, and it is why T2’s design matters more than its one-line proof.

The manual axiom check for T1/T2 is clean (`[propext, Quot.sound]`), which is what the plan expects. The absence of `sorry` is verified by grep. Neither is a substitute for the audit gate (F9), but both are good signs.

---

## 9. Handoff checklist for M2/M3

Ordered by risk, not by effort:

1. **Fix F1** (`maxPoint` recursion) and add the branch-tail + target-range tests. Do not merge M1 without this.
2. **Fix F3** (`Program.safe` namespace) and add a `#check Program.safe`/dot-notation test.
3. **Add F2** (`CFG.WF` + `Program.compile_wf`) and a test that every `cfg.edges` destination is in range. This is the hypothesis T5 will need.
4. **Add F4** (`step_edge`), including the `assume` polarity cases; this is the bridge between `step` and the checker.
5. **Settle F5** before M2.6: `transfer : EdgeCmd → Abs → Abs`, `entails : Abs → BExp → Bool`, the edge semantics for `assume`, and the point-space definition. Update `Domain.lean`, `Check.lean`, `THEOREMS.md` T4/T5, and `certificate-v1.md` §12.6.
6. **Add `Program.WF`** (dense unique points, arrays/vars in range, bounded `maxPoint`) and enforce it at the frontend (F7/F11). This is TCB assurance, not a T5 blocker, but it is cheap now.
7. **Update docs** (F8): README M1 status, `known-gaps.md`, the `Semantics.lean` header, `TCB.md` parser row, roadmap `div` wording, and the branch/merge note. Tag M1 after 1–6.
8. **Audit T1/T2** (F9) and make `Audit.lean` non-empty.
9. **Add an aggregate test runner** and a `Compile.lean` shape table (F10).
10. **Decide strict booleans** (F6) and record the outcome in `known-gaps.md`/the paper, with the statement-level idiom in the examples.
11. **Merge to `main`** and let CI exercise the M1 tests on the protected branch.

The first four are the real exit work. The rest are hygiene that pays for itself before M3.

---

## 10. Bottom line

M1 is a good milestone. The hard conceptual choice — define safety as `none`, compile to an edge machine, and make `Safe` a finite-prefix property — is made, implemented in a small amount of readable Lean, and tested. The proof shape for T5 is credible: init from `State.init`, edge transfer from `transfer_sound`, safety from `entails_sound`, and an induction on `run` via `safe_iff_exists`.

But the milestone is not merge-ready. **F1 is a real bug in the trusted compiler**, not a theoretical concern: a loop or `if` whose body has the highest point is silently truncated, and the existing examples pass by accident. **F3** is a public-API bug that will bite T5 and anyone following the docs. **F2** and **F4** are the missing theorems that turn the current definitions into a proof-ready interface.

The reassuring part is that all four are cheap: two lines for F1, a namespace move for F3, and two short lemmas for F2/F4. If they are closed before M2, T5 has a clean path. If M1 is declared done now, M3 will meet them as proof obligations under gate pressure, and F1 will look like a semantics bug rather than a compiler bug. Fix them first, then call M1 done.

---

## 11. Post-review updates

**2026-11-25.**

- **F1 fixed** in commits `2d8dfc5`–`4ddab91`: `Cmd.maxPoint` now recurses into
  `if`/`while` bodies, `Cmd.entry` is total, and `instrAt` uses a safe
  in-range array access. The branch-tail case now compiles to the full
  instruction array.
- **F2 fixed**: `CFG.WF`, `Program.compile_wf`, and the supporting lemmas
  (`Cmd.entry_le_maxPoint`, `Cmd.place_targetsLt`, `Cmd.compile_size`,
  `Cmd.compile_targetsLt`, `Instr.edgesAt_dst_lt`, `CFG.WF.edges_dst_lt`) are
  in `Semantics.lean`. `Tests/Compile.lean` pins the `maxPoint` bounds, array
  sizes, target ranges, branch-tail reachability, and the theorem at the
  expected type. CI and the README list the new test.
- **F3 fixed**: `Program.safe` now lives in `namespace Program`, so
  `CertCore.Program.safe` and dot notation `p.safe` both work.
  `Tests/Run.lean` pins the name, dot notation, and the definitional unfolding
  against `CFG.Safe (Program.compile p) (State.init p)`.
- **F4 fixed**: `EdgeCmd.exec` gives the effect of a checker edge, and
  `CFG.step_edge` proves that every successful `step` is an edge in `cfg.edges`
  with the same source, destination, and edge effect. `Tests/Edges.lean` pins
  the atomic and branch cases and the `assume`-edge effect.
- `Tests/Syntax.lean` was updated for the now-total `Cmd.entry`.
- **F7 partly fixed**: `Cmd.entry` and `Program.entry` are now total, `instrAt`
  uses an in-range lookup, and `Program.compile_wf` makes out-of-range writes
  unreachable for compiled programs. `place` remains fail-open for malformed
  CFGs; a frontend `Program.WF` (dense/unique points, array/variable bounds) is
  still M4/M5 work.
- **F8/F9 closed for M1**: README, TCB, known-gaps, and the stub headers now
  describe M1; `Audit.lean` prints the T1/T2, `compile_wf`, and `step_edge`
  footprints. F10 (aggregate test runner) remains optional hygiene.
- Verified after the changes: `lake build` green, no warnings; all nine test
  files pass; no `sorry`; the audit footprint is `[propext, Quot.sound]` for
  every printed M1 lemma.
