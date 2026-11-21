# CertCore from zero

**An introduction to verified static analysis, told through this project.**

You can read code, but you have never studied abstract interpretation or proof
assistants. This document is for you. It explains every piece of jargon the
project uses, with examples from CertCore itself, and builds up to the point
where the plan and the code become readable.

By the end you should be able to say, in plain words:

1. what CertCore actually proves, and for what kind of program;
2. why the analyzer is deliberately untrusted, and why that is a feature;
3. what a certificate contains, and why a table of number ranges is enough;
4. what "precision costs bytes" means, and why the project measures it.

Suggested order: this document, then §0–§5 of the
[project plan](certcore-project-plan.md), then the
[wire format](certificate-v1.md) and [theorem contract](THEOREMS.md).

---

## 1. The question this project answers

### 1.1 A verdict you cannot check

Look at this program:

```text
x := 1
y := 10 / x
```

No division by zero — you can see it. Now:

```text
x := read_input()
y := 10 / x
```

This one divides by zero whenever the input is 0. You can still see it. Now
imagine ten thousand lines, loops, arrays, and arithmetic that overflows. At
some point you cannot see it any more, and you need a tool.

A **static analyzer** is a program that answers "safe" or "unsafe" without
running the program. Industry uses them on avionics and medical code, where a
wrong "safe" is not an inconvenience but a recall, or worse.

So: the analyzer says "safe". Why should anyone believe it?

An analyzer is itself a large program. Inside are a fixpoint computation, a
widening heuristic, array and integer arithmetic, and a parser. Any one of those
can have a bug. When a commercial vendor says "no runtime errors", the customer
is being asked to trust several hundred thousand lines of unverified code. This
is the *trust problem* the project starts from (plan §1.2).

### 1.2 Two ways to make a verdict trustworthy

**Answer A — verify the analyzer.** Prove, in a proof assistant, that the
analysis engine itself never lies. This is what Verasco did for a C analyzer
(POPL 2015): a Coq development in which the fixpoint engine is proved sound.

This is genuinely impressive, and it has a cost: the analyzer is now *inside*
the trusted base. Every new analysis, every new domain, every optimisation needs
a new proof by the same authors. And it does not help at all when the analyzer
is a language model or a hybrid search procedure, which is increasingly what
produces invariants in 2026.

**Answer B — verify the certificate.** Let the analyzer be untrusted. Require it
to emit a **certificate**: a piece of data that witnesses its claim. A small
**checker** — small enough to audit, small enough to prove correct — verifies the
certificate against the program's semantics. If the checker accepts, the program
is safe; if the analyzer cheated, the certificate is rejected.

This is **proof-carrying code** (PCC), invented by Necula and Lee in 1997. The
checker does not trust the producer; it re-checks the evidence. The classic
analogy is a proof checker in mathematics: it does not invent the proof, but it
verifies every step, and its own correctness is a small, auditable thing.

CertCore takes Answer B. The one-sentence design, from plan §17:

> **Move every source of cleverness outside the trusted base, and make the
> certificate the only interface.**

Everything else follows. The checker performs **no search** (so it is fast and
predictable). The analyzer can be written in any language, or replaced by a
model (so the guarantee survives). The certificate is plain JSON (so a human,
a tool, or a language model can produce and inspect one).

### 1.3 What is new here, honestly

Not the architecture — PCC over abstract interpretation is twenty years old.
The project's claims, after the prior-art check in
[prior-art.md](prior-art.md), are narrower and more defensible:

- one **fixed** checker program, parametric in a description of an abstract
  domain, rather than a new checker per domain;
- **combinators** that add precision (product, and post-month reduced product)
  without touching the checker;
- **path sensitivity as a product**, mechanised and certifying (the theory is
  classic; the mechanised certificate instance is not);
- a measured **frontier** of precision against certificate size — the figure
  the project is really about.

Read [prior-art.md](prior-art.md) before repeating any stronger claim. It also
corrects one factual error in the plan about the 2006 predecessor.

---

## 2. The smallest possible tour

The full pipeline has two processes and one protocol:

```text
  source .imp  ──▶  Lean frontend  ──▶  AST.json
                    (trusted)             │
                                          ▼
                            Haskell analyzer (untrusted)
                            fixpoint + widening + labels
                                          │
                                          ▼
                                   certificate.json
                                          │
                                          ▼
                    Lean decoder + checker (trusted)
                    init / edge / safety obligations
                                          │
                                          ▼
                              accept  or  Diagnostic
```

| Stage | Language | Trusted? | If it fails |
|---|---|---|---|
| Parse source, build CFG | Lean | **yes** | reject the program |
| Compute invariants | Haskell | no | may emit no certificate |
| Decode certificate | Lean | **yes** | `malformed` |
| Check obligations | Lean | **yes** | a diagnostic naming the failure |
| Verdict | Lean | **yes** | safe / rejected |

The commands, once M4 and M5 land, look like this:

```console
$ certcore analyze examples/div.imp
analyzer: safe; wrote cert.json

$ certcore check examples/div.imp cert.json
ACCEPT: 3 obligations, 3 ble calls, 0.4 ms
```

Then the demo's punchline: edit one number in `cert.json` and re-run.

```console
$ certcore check examples/div.imp cert.json
REJECT: Diagnostic.edge point=1 expected=[1,1] actual=[1,6]
```

The checker caught a lie in milliseconds. That rejection is a *value*, not a
string: the untrusted analyzer can read it and try again.

> **Status, honestly.** At the time of writing the repository is at milestone
> M0: the build, the format and the gates exist; the checker does not yet. The
> commands above are the target, not the present.

---

## 3. What "safe" means in this project

Before anything can be proved, "safe" must be defined by mathematics rather than
by a document nobody checks. CertCore defines it with a **small-step
operational semantics**: a description of what one execution step does.

### 3.1 States and steps

A **state** assigns a 32-bit integer to every variable and a value to every
array cell. A **step** executes one command and returns either the next state or
"went wrong":

```text
step : Command → State → Option State
```

`none` means a bad thing happened. In CertCore's language, `Imp`, the bad
things are exactly the safety properties under test (plan §8.1):

- division by zero;
- signed 32-bit **overflow** (the machine integer would wrap; here that is an
  error, not a wrap-around);
- an array index outside its bounds;
- a failed `assert`.

Everything else is `some next_state`.

### 3.2 Fuel, and why infinite loops are safe

Running a program forever is not something a definition can do directly. So the
semantics is **fuel-indexed**: `run n s` performs at most `n` steps.

```text
Safe s  :=  ∀ n, run n s ≠ none
```

Read it as: no finite number of steps ever goes wrong. Consequences:

- A program that loops forever is **safe**, because every finite prefix is fine.
  In this project "safe" means "no division by zero, no overflow, no bad
  access" — not "terminates".
- The definition avoids coinduction and termination side conditions. Every later
  proof is an ordinary induction on `n` (plan D6). This is a deliberate
  engineering choice, and T2 in the [theorem contract](THEOREMS.md) exists to
  keep it usable.

### 3.3 Why the semantics is trusted

If `step` has a bug — say it forgets to check overflow — then "safe" silently
means something weaker, and every certificate is a certificate about the wrong
language. So the parser and the semantics live in Lean, in the trusted base,
reviewed as one small file. The plan calls this the shrinking-the-TCB choice
(D5).

---

## 4. Abstraction: trading detail for certainty

You cannot list every reachable state of a loop with a million iterations. So
the analysis works with **abstract states**: compact descriptions that stand for
sets of concrete states.

### 4.1 The one idea

An **abstract domain** is a set of descriptions, plus a function

```text
γ : AbstractState → Set ConcreteState
```

read "gamma". `γ(a)` is the set of concrete states that the description `a`
stands for. This is the **concretisation** function; it is how the abstract
world is tied to reality.

In CertCore the primary domain is **intervals** (plan M2). An abstract state maps
each variable to an interval:

```text
{ x ↦ [0, 10], y ↦ [-5, -1] }
```

and its meaning is: all states where `0 ≤ x ≤ 10` and `-5 ≤ y ≤ -1`. A variable
that is absent is unconstrained — that is **top** (`⊤`). The empty set of states
is **bottom** (`⊥`).

### 4.2 Inclusion: one abstract state inside another

The checker's entire decision procedure is one question, asked many times:

> Is every state described by `a` also described by `b`?

That is **inclusion**, written `a ≤ b` or `γ(a) ⊆ γ(b)`. For intervals it is a
comparison of endpoints: `[0,5]` is inside `[0,10]`; `[0,10]` is not inside
`[0,5]`. The executable version is called `ble` ("bool less-or-equal"):

```text
ble : AbstractState → AbstractState → Bool
ble_sound : ble a b = true → γ(a) ⊆ γ(b)
```

`ble` is a `Bool` because the checker must *run* and be fast. `⊆` is a
*proposition* because the proof must be *about the real thing*. The lemma
`ble_sound` is the bridge between the two worlds, and it is where most of the
engineering care goes (plan §4.2, D7).

### 4.3 Transfer: what a command does to a description

A **transfer function** says how a command transforms an abstract state:

```text
transfer : Command → AbstractState → AbstractState
```

If `x ∈ [0,5]`, then after `x := x + 1` we know `x ∈ [1,6]`. If
`x ∈ [1,5]`, then after `y := 10 / x` we know `y ∈ [2,10]`.

A transfer function is allowed to be imprecise — it may return a bigger interval
than necessary — but it must never be smaller (that would be unsound):

```text
transfer_sound : s ∈ γ(a) → step c s = some s' → s' ∈ γ(transfer c a)
```

### 4.4 Join: merging two descriptions

At a point where two control-flow paths meet, the analysis must merge the two
descriptions. **Join** is the smallest abstract state containing both:

```text
[0,2] ⊔ [5,7]  =  [0,7]
```

The gap between 2 and 7 is lost. This is the fundamental trade: a description
that is cheap to store and compare cannot remember that a value is *never* 3.
Section 8 shows how the project buys that memory back.

### 4.5 What abstraction costs you

```text
if x >= 0 then y := 1 else y := -1
assert (y != 0)
```

Both branches are fine: `y` is 1 or -1, never 0. But the merged interval is
`[-1,1]`, which contains 0, so the interval analysis cannot prove the assertion.
This is not a bug in the analysis; it is the information the domain chose to
forget. Keep this example in mind — it comes back in §8.3.

---

## 5. The certificate is an inductive invariant

Now the central idea of the whole project.

### 5.1 Program points and edges

The trusted frontend turns the program into a **control-flow graph** (CFG): a
set of numbered **program points** and **edges** `(p, command, q)` meaning
"executing `command` at point `p` can lead to point `q`". Loops make this graph
cyclic, which is why naive evaluation never terminates.

### 5.2 The table

A certificate supplies an abstract state for (some) program points. For the
running example

```text
0: x := 0
1: x := x + 1
2: y := 10 / x
3: assert (y == 10)
```

the table can be:

| Point | Abstract state |
|---|---|
| 0 (entry) | `{}` (everything unconstrained) |
| 1 | `{x ↦ [0,0]}` |
| 2 | `{x ↦ [1,1]}` |
| 3 | `{x ↦ [1,1], y ↦ [10,10]}` |

Call it `I`. It is not computed by the checker; it arrives from the untrusted
analyzer. What makes it a certificate is that it is **inductive**:

- **init** — every initial concrete state is described by `I(entry)`;
- **edge** — for every edge `(p, c, q)`: every state after running `c` from a
  state in `γ(I(p))` lies in `γ(I(q))`;
- **safety** — at every point where a partial operation occurs, `I(p)` rules out
  the bad case (division by zero, out-of-bounds index, overflow, false assert).

The checker verifies exactly these three families. Nothing else.

### 5.3 Why the table implies safety

This is the one proof worth reading, and it is short.

Claim: every state that can actually occur at point `p` lies in `γ(I(p))`.

- *Base.* The initial state lies in `γ(I(entry))` by the init obligation.
- *Step.* Suppose a state `s` occurs at `p` and lies in `γ(I(p))`, and the
  program takes edge `(p, c, q)` to `s'`. By transfer soundness,
  `s' ∈ γ(transfer c (I(p)))`. By the edge obligation and `ble_sound`,
  `γ(transfer c (I(p))) ⊆ γ(I(q))`. So `s' ∈ γ(I(q))`.
- By induction over executions, every reachable state lies in its point's
  abstract state.

Now suppose a step goes wrong at point `p`. The state `s` before it is reachable,
so `s ∈ γ(I(p))`. But the safety obligation says `I(p)` rules the failure out —
contradiction. Therefore no step ever goes wrong, for *any* number of steps:
`Safe` holds.

This argument is T5, `check_sound`, and it is the theorem the whole project
exists to state once and for all domains (plan §4.6):

```text
check_sound : check D p c = .ok → Safe p
```

Notice what it does *not* say: it does not say the analyzer is correct, or the
invariant is the most precise one, or the analysis terminates. It says: **if the
checker accepts this table, the program is safe.**

### 5.4 The checker does not search

Every obligation is one `ble` call — or one entailment test for safety
predicates. There is no fixpoint, no backtracking, no matching, no SMT solver.
That is why checker time is linear in the certificate size, and why a hostile
certificate cannot make the checker run for hours (requirement R4, plan §5).

The search happened earlier, in the analyzer. CertCore's bet is that **search is
untrusted and checking is trusted** — the cheapest possible split.

### 5.5 Rejection is a value

When an obligation fails, `check` returns a `Diagnostic` naming the point, the
label, the command, the obligation kind, and the expected and actual states:

```text
Diagnostic.edge point=1 expected=[1,1] actual=[1,6]
```

This is deliberately a data structure rather than a log message, because the
untrusted analyzer consumes it programmatically: on rejection it relaxes the
certificate and retries (M5.6). It is also the feedback channel a language model
would need to propose better invariants (requirement R6).

### 5.6 Sparse certificates, and why omission is safe

A certificate may omit points. A missing `(point, label)` entry is interpreted
as **top** — "anything could happen here". Omitting states costs precision (the
safety check at that point must then hold for every possible state) but cannot
buy a false acceptance. Rejecting missing entries instead would force the
checker to compute reachability, which is search — forbidden by R4.

---

## 6. What "verified" means here

### 6.1 Lean in one page

Lean 4 is a programming language and a **proof assistant**. Two facts are enough
to read this project:

1. **Propositions are types, proofs are programs.** A theorem is a function
   whose type says what it proves; checking the proof is type-checking.
2. **The kernel is small.** A tiny core verifies every proof term. Everything
   else — the elaboration, the tactics, the automation — is untrusted, because a
   bug there produces a term the kernel rejects.

Lean also *executes*: `#eval check p c` runs the checker by compilation, in the
same file as `theorem check_sound`. That combination — an executable checker and
its soundness proof in one language — is why the plan chose Lean over Coq or
Isabelle (D1).

### 6.2 Bool and Prop: the reflection boundary

The checker must answer "is `a` inside `b`?" quickly, so `ble` returns a
`Bool` and compiles to machine code. The theorem is about sets, which live in
`Prop`. The two are connected by a proved lemma, `ble_sound`, and this pattern
recurs for every domain operation. It is duller than using `Decidable`
everywhere, but it gives a predictable cost model and keeps `#eval` fast (D7).

### 6.3 Axioms, `sorry`, and the audit

A proof can rest on assumptions. Lean records them, and one command lists them:

```console
$ lake env lean lean/CertCore/Audit.lean
#print axioms check_sound
-- 'check_sound' depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are standard, benign principles of Lean's logic. What
must never appear:

- `sorryAx` — the axiom introduced by the placeholder `sorry`, which lets a
  "proof" be admitted without a proof;
- `Classical.choice` — classical reasoning the project does not intend to need.

So the audit is a grep for silent holes, and CI runs it. Two limits deserve
saying plainly: the audit checks the *proof*, not the Lean compiler, the
operating system, or the hardware (see [TCB.md](TCB.md)); and a `sorry`
elsewhere in the tree would not be caught unless the audit covers it, which is
why the `sorry` grep exists as a second, cruder gate.

### 6.4 Two things called "kernel"

A confusion worth killing early:

- **Lean's kernel** — the small trusted core that checks proof terms. It is part
  of the foundation, and nothing in this project proves it correct.
- **CertCore's kernel** — the checker plus the semantics plus the one generic
  soundness theorem. This is what the project calls small and auditable.

When the documents say "the kernel", context decides. §17 of the plan means the
second one.

### 6.5 The contract has two sides

Soundness alone is cheap: a checker that rejects everything is sound and
useless. So the project also proves acceptance:

```text
encode_accepts : IsPostFixpoint p I → check D p (encode p I) = .ok
```

Every genuine inductive invariant has a certificate the checker accepts. A
reviewer asks for this; most certifying prototypes cannot even state it (plan
§4.2). T5 and T8 together are the contract.

---

## 7. The trust boundary

The **trusted computing base** (TCB) is everything whose bug could produce a
wrong verdict. CertCore's is deliberately tiny ([TCB.md](TCB.md)):

| Inside | Outside |
|---|---|
| Lean kernel and toolchain | the Haskell analyzer |
| parser and CFG construction | widening, thresholds, heuristics |
| the semantics (`step`, `Safe`) | label instrumentation decisions |
| the JSON decoder | the Python benchmark harness |
| the checker and its proof | the certificate bytes themselves |

Why write the analyzer in a *different language*? Not style: it makes the
boundary architectural. If the analyzer and checker implement the transfer
function differently, the checker catches the disagreement at the boundary — and
that disagreement is data (the differential test, M5.7). A bug in the analyzer
produces a rejected certificate, never a wrong verdict.

Why JSON? Because a human can read a rejected certificate, and a tool — or a
language model — can emit one. The verbosity is real, and §9 treats it as the
measured cost rather than hiding it (plan D4).

---

## 8. Buying precision without touching the checker

The checker is generic over a **`CertDomain`**: a bundle of an abstract state
type, `γ`, `ble`, `ble_sound`, `top`, `join`, `transfer`, and each operation's
soundness proof. Add a domain by filling in the bundle, not by editing the
checker. That is requirement R5.

### 8.1 Product: the cheapest precision

A **product domain** pairs two domains: the state is a pair, every operation acts
componentwise, and `γ` is intersection. If one component tracks value ranges and
the other tracks parity, the pair knows both facts about the same variable.

Because `CertDomain` is a structure rather than a class hierarchy, the product is
just another instance. There is no new theorem about certificates to prove; the
component proofs compose. M6's acceptance test is one sentence: **zero lines
changed in `Check.lean`.**

### 8.2 Reduced product: when the components talk

In a plain product, an interval `x ∈ [0,10]` and a relational fact `x = y` do not
inform each other. A **reduced product** adds a reduction `ρ` that pushes facts
both ways: from `x = y` and `x ≤ 10`, derive `y ≤ 10`.

This is where it gets subtle, and why the roadmap makes it post-month (M8). The
checker cannot recompute the reduction during checking without re-running the
analysis — that would be a search. So the certificate must record **which
reductions fired**: the hints. The obligation (T7) is that replaying the hints
produces a state that is still a post-fixpoint, which needs the reduction to be
*sound* and *idempotent*. It is the most intellectually risky theorem in the
plan, and deliberately outside the four-week scope.

### 8.3 Path sensitivity: the example that motivates labels

Return to the program from §4.5:

```text
0: if (x >= 0) { 1: y := 1 } else { 2: y := -1 }
3: assert (y != 0)
```

With plain intervals, `I(3) = {y ↦ [-1,1]}`, and the assertion is not provable:
the interval contains 0. Yet *no execution* reaches 0. The information exists;
the domain threw it away at the join.

Three ways to keep it:

1. **Disjunctive domain** — let an abstract state be a *set* of intervals. Precise,
   but now inclusion between two sets of intervals is a matching problem: which
   interval goes with which? That is a search, and in general NP-hard. It
   violates the no-search rule (R4), and the plan explicitly declines it (plan
   §7.5).
2. **Unroll the program** — duplicates the CFG for every path; exponential.
3. **Partition by a label** — keep a small, *finite* token that records which
   branch was taken, and give every `(point, label)` pair its own abstract state.

CertCore takes (3). The token is called a **label** `κ`, the finite set is `K`,
and the construction is:

```text
D_labelled  :=  D × Flat(K)
```

where `Flat(K)` is the flat lattice over `{0, …, K−1}`: distinct labels are
incomparable, so its inclusion test is equality (plus top) — one comparison.
The label is updated by the semantics itself: for a branch-history scheme,
`κ' = ((κ << 1) | outcome) mod 2^k` — the last `k` branch outcomes, most recent
bit first. The semantics is **instrumented**, not changed: T9 proves that
projecting the label away recovers the ordinary semantics, and that errors are
preserved.

With `k = 1`, the example above has two labels. At point 3 there are two states:

| Point | Label | State |
|---|---|---|
| 3 | 0 (one branch) | `{y ↦ [1,1]}` |
| 3 | 1 (the other branch) | `{y ↦ [-1,-1]}` |

Each excludes 0, so the assertion is proved. The certificate grew by one entry;
precision was bought with bytes.

The architectural payoff: no new certificate theory, no new inclusion check, and
no new soundness proof per partition — T9 is proved once for the instrumentation.
Path sensitivity is a *product instance*, and the cost shows up where the project
measures it — in certificate size.

### 8.4 What the analyzer can still do wrong

Plenty: an unsound widening, a missed edge, a bogus label. Every one of those
produces a certificate the checker rejects. That is the whole design: the
analyzer is allowed to be brilliant or broken, and the verdict does not move.

---

## 9. The frontier: precision for sale

The project's headline claim is empirical, not logical:

> Precision is purchasable with certificate bytes, at a rate we can measure,
> while checker cost stays flat and the trusted base stays fixed.

This is the **north-star experiment** (plan §13). Roughly thirty benchmark
programs in five families — straight-line code, loops needing widening, array
bounds, path-sensitive programs, and small kernels like binary search — are run
through the analyzer at label depths 0, 1 and 2. For each program and depth:

- is it certified safe? (yes/no)
- how many bytes is the certificate?
- how long does checking take?

The plot puts **certificate bytes** on the horizontal axis and the **number of
programs certified** on the vertical axis, one curve per depth, with checking
time overlaid. The intended picture is a curve that rises steeply and flattens:
the first few hundred bytes buy most of the precision, and the checker's line
stays near the floor.

Why the shape matters: everyone *assumes* expressive certificates are big and
hard to check. The project turns the folklore into a curve. If the curve is bad
— bytes explode before precision improves — that is a finding, not a failure,
and it gets reported (gate G3, plan §12.4).

Two honest caveats, stated up front in the plan: there is no head-to-head
baseline against Verasco or Astrée (different language, different decade), and
thirty programs establish *shape*, not scalability.

---

## 10. Hostile input is part of the problem

In a verified *analyzer*, the input is a program. In a certifying system, the
input includes bytes from an adversary. A malformed certificate must be a
rejection, never a crash, and must not be able to make the checker do
super-linear work (T10).

Concretely, the decoder rejects:

- unknown fields and wrong types — strictness is deliberate;
- points outside the program, labels outside `[0, K)`, duplicate keys;
- an interval with `lo > hi` (the classic soundness trap: `[5,3]` would make
  "contained in everything" true);
- an explicit unbounded interval, since top is encoded by omission;
- a `labels.size` outside `[1, 64]`, which bounds the work a certificate can ask
  for;
- a `program_hash` that does not match the AST.

Then the fuzzer mutates ten thousand valid certificates — flip a bound, drop a
state, swap a point — and the target is **zero accepts and zero crashes**. An
accepted mutation is a soundness bug and becomes a regression test (M10.3,
M11.1).

---

## 11. Where the project stands

The plan is a four-week schedule with four gates (roadmap §12):

| Gate | Day | Question | If "no" |
|---|---|---|---|
| **G1a** | 5 | Does T5 close as a short induction on a toy semantics? | redesign the semantics |
| **G1b** | 7 | Is `check_sound` closed for the real interval semantics? | cut labels, ship intervals only |
| **G2** | 10 | Does a Haskell certificate get accepted by a Lean checker it never talked to? | fall back to a Lean driver |
| **G3** | 15 | Does the frontier plot exist? | the paper becomes a design paper |

At M0, the repository contains: the pinned toolchain, the empty trusted tree, the
frozen wire format, the theorem contract, the trust-boundary document, the
prior-art check, and CI that fails on a `sorry` or a broken audit. The checker
itself is M2–M4.

---

## 12. Glossary

Terms are defined here in the sense this project uses them.

| Term | Meaning |
|---|---|
| **Abstract domain** | A set of compact descriptions of sets of states, with operations (`ble`, `join`, `transfer`) that are sound with respect to a concretisation `γ`. |
| **Abstract state** | One element of an abstract domain. Here: a map from variables to intervals, or bottom. |
| **Abstraction (α)** | The map from sets of concrete states to abstract descriptions. CertCore's interface never needs it; only `γ` and soundness are required. |
| **Axiom** | An assumption a proof rests on, listed by `#print axioms`. `propext` and `Quot.sound` are expected; `sorryAx` is a hole. |
| **Bottom (⊥)** | The abstract state describing no concrete states: an unreachable point. |
| **Certificate** | The untrusted data a producer emits to justify a verdict: here, a JSON table of `(point, label) → abstract state`. |
| **Certifying algorithm** | An algorithm that returns its answer together with a witness that a cheaper checker can verify. |
| **Checker** | The trusted program that validates a certificate. Performs no search. |
| **Completeness** | Of an analysis: reporting no false alarms. Unreachable in general; the checker instead is *sound*, and its inclusion test is incomplete for some domains. |
| **Concretisation (γ)** | `γ(a)` is the set of concrete states an abstract state stands for. |
| **Diagnostic** | The structured value returned on rejection: point, label, edge, obligation, expected and actual states. |
| **Disjunctive completion** | A domain whose elements are sets of abstract states. Precise, but inclusion becomes a matching search; declined here. |
| **Fixpoint / post-fixpoint** | A map `I` that the transfer function does not increase. A *post*-fixpoint suffices: the checker verifies inductiveness, not minimality. |
| **Fuel** | A step bound (`run n`), used to define safety without coinduction. |
| **Galois connection** | The classical adjunction between `α` and `γ`. CertCore uses only the `γ` half. |
| **Inductive invariant** | A table of abstract states preserved by every edge from the entry. The certificate *is* one. |
| **Interval domain** | The domain whose states map variables to intervals `[lo, hi]`. The first domain implemented (M2). |
| **Join (⊔)** | Least upper bound: the smallest abstract state containing both inputs. Merging paths loses information here. |
| **Kernel (Lean)** | The small core that type-checks proof terms. Trusted as a foundation. |
| **Kernel (CertCore)** | The semantics, decoder, checker, and the generic soundness theorem. The project's small trusted core. |
| **Label (κ)** | A token from a finite set recording which path a state came from; the basis of path sensitivity. |
| **Lean 4** | The proof assistant and programming language used for the trusted side; proofs and executable code coexist. |
| **Octagon domain** | States of the form `±x ± y ≤ c`: relational, more precise than intervals (e.g. `x = y`). Post-month (M7). |
| **Path sensitivity** | Keeping different facts for different control-flow paths instead of merging them. |
| **PCC (proof-carrying code)** | The architecture: untrusted producer ships code plus a certificate; a small trusted checker validates it. |
| **Precision** | How much a domain can say; measured here by how many benchmark programs are certified. |
| **Product domain** | The componentwise pairing of two domains. Adds precision with no new checker and no new proof about certificates. |
| **Proof assistant** | A tool in which proofs are checked by machine (Lean, Coq, Isabelle). |
| **Reduced product** | A product plus a reduction that exchanges facts between components; needs recorded hints to stay checkable (post-month, T7). |
| **Reflection** | Proving that an executable `Bool` test agrees with the mathematical `Prop` statement it implements, e.g. `ble_sound`. |
| **Safety property** | "Nothing bad happens": here, no division by zero, overflow, out-of-bounds access, or failed assertion. |
| **Small-step semantics** | A definition of one execution step at a time, as opposed to a whole-run relation. |
| **Soundness** | An over-approximation: never claims a state is impossible when it is possible. The checker's acceptance implies real safety. |
| **`sorry`** | Lean's placeholder for an omitted proof. Compiles, but introduces `sorryAx`; banned in the trusted tree. |
| **TCB** | Trusted computing base: everything whose bug could make a verdict wrong. |
| **Top (⊤)** | The abstract state describing all states: no information. Encoded by omission in the wire format. |
| **Trace partitioning** | The classical technique of analysing a partition of executions; the theory behind labels. |
| **Transfer function** | The abstract effect of a command: `transfer c a` over-approximates the post-states of `γ(a)`. |
| **Widening** | A deliberate over-approximation used to make a fixpoint converge. May be unsound; an unsound widening yields a rejected certificate. |
| **Witness** | Data that makes a claim checkable without redoing the work that found it. A certificate is a witness. |

---

## 13. Eight misconceptions

1. **"The checker proves the analyzer is correct."** No. It proves the
   *certificate*. The analyzer may be wrong, heuristic, or a language model; a
   bad analyzer yields a rejected certificate, not a wrong verdict.
2. **"The certificate is a proof script."** It is a table of number ranges. The
   proof is one generic theorem, proved once, that any inductive table implies
   safety.
3. **"Safe means the program terminates."** No. A non-terminating program is
   safe if no finite prefix goes wrong. `Safe s := ∀ n, run n s ≠ none` is
   deliberate.
4. **"One `ble` call proves the whole program."** One `ble` decides one
   obligation. The global argument is the induction in §5.3; the semantics and
   that induction are what make the per-obligation calls mean something.
5. **"The program hash prevents forged certificates."** It detects a certificate
   for the wrong program, as a courtesy diagnostic. Even with a hash collision,
   every obligation is still checked against the real AST.
6. **"Lean's kernel is CertCore's kernel."** Two different things; see §6.4.
7. **"More precision is always better."** Precision costs certificate bytes and
   checking time. The project's entire point is to measure the exchange rate, not
   to maximise one side of it.
8. **"The checker accepts every true invariant."** No. Inclusion is incomplete
   for some domains (notably octagons): a valid invariant can be rejected. This
   is a documented limitation, not a bug ([known-gaps.md](known-gaps.md)).

---

## 14. Reading map

| If you want to know… | Read |
|---|---|
| why the project exists, in the author's words | [plan §1–§3](certcore-project-plan.md) |
| the exact theorem list and status | [THEOREMS.md](THEOREMS.md) |
| the wire format, field by field | [certificate-v1.md](certificate-v1.md) |
| what is trusted and what is assumed | [TCB.md](TCB.md) |
| what is already published, and what is actually new | [prior-art.md](prior-art.md) |
| what is deliberately not attempted | [NONGOALS.md](NONGOALS.md) |
| the schedule, gates and cut order | [roadmap](certcore-roadmap.md) |
| any known gap | [known-gaps.md](known-gaps.md) |

Three things worth remembering when you close this document:

1. The certificate is an **inductive invariant**, and the checker verifies it
   with **no search**.
2. The analyzer is **untrusted by construction**; the trust boundary is a
   property of the architecture, not a promise.
3. Precision is **bought with bytes**, and the project's deliverable is the
   measured exchange rate.
