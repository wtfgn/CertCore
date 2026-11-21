# CertCore — A Verified Certificate Kernel for Abstract Interpretation

**Buying precision with certificate size, at a fixed trusted computing base.**

| | |
|---|---|
| **Status** | Project plan, v1 — ready to execute |
| **Duration** | 4 weeks (20 working days) + 2 days prep |
| **Primary language** | Lean 4 (proofs + checker), Haskell (untrusted analyzer) |
| **Deliverable** | Open-source artifact: verified checker, untrusted analyzer, benchmark suite, theorem inventory, evaluation |
| **Codename** | `CertCore` |

---

## 0. Executive summary

CertCore is a **domain-generic, mechanically verified certificate kernel for abstract-interpretation-based static analysis**, plus an *untrusted* analyzer that drives it. The analyzer — written in Haskell, deliberately outside the trusted base — computes an invariant map and emits a certificate. A small Lean 4 checker validates the certificate against a formal semantics. If the checker accepts, the program is safe, as a kernel-checked theorem.

The kernel is parameterised by a `CertDomain` structure: any abstract domain supplying a concretisation function and a *sound, executable* inclusion test yields a sound checker, by a single generic theorem proved once. On top of that we build **verified certificate combinators** — product and reduced product — and show that *path-sensitive analysis does not require a new certificate theory at all*: it is the product of the base domain with a finite label domain whose transfer function is derived from the semantics.

The headline empirical claim is the thesis of the project:

> **Precision is purchasable with certificate bytes, at a rate we can measure, while checker cost stays linear and the trusted base stays fixed.**

This turns the field's folklore tradeoff — "expressive certificates are big and hard to check" — into a measured curve. The project's north-star figure is a plot of *programs proven safe* against *certificate size*, parameterised by numerical domain (intervals → octagons) and partition depth, with checker time overlaid as a near-flat line.

**What is genuinely new** is not the architecture (proof-carrying code over abstract interpretation is 20 years old) but a specific point in the design space that nobody currently occupies: *verified, composable, domain-generic certificate checking with an executable checker and a measured expressiveness/cost frontier*. Section 7 states this precisely and honestly, including what is borrowed and what a hostile reviewer will say.

**On the name.** *CertCore* names the two things that are actually ours: the **cert**ificate is the interface, and the **core** is the small trusted kernel that validates it. It is deliberately descriptive rather than metaphorical — the field's metaphorical names (Iris, Bedrock, Verdi) age well but say nothing, while the descriptive ones (CompCert, CakeML, VeriFast) name the mechanism. `certcore check prog.imp cert.json` composes as a command, which is the test that killed several candidates.

---

## 1. Why build this

### 1.1 A plan document, first, because the month is the constraint

A one-month project fails in one of two ways: it drifts (scope grows until nothing is finished), or it stalls (one unproven lemma eats three weeks). Both are managed by writing the plan first. The artefact below exists to make three things auditable in advance: the **theorem contract** (§4.6 — exactly what will be proven), the **scope fence** (§8 — exactly what will not be attempted), and the **kill criteria** (§12.4 — the date at which we admit defeat and ship a smaller thing). Everything else in this document is subordinate to those three.

### 1.2 The trust problem is the field's actual bottleneck

Static analyzers are asked to be believed. Astrée's soundness argument is a paper proof over an unverified OCaml implementation of several hundred thousand lines. A commercial analyzer's "no runtime errors" verdict is, from the customer's perspective, an assertion. This is a strange state of affairs for a discipline that invented machine-checked proof: the *analysis* is the one part of the safety argument that is usually not mechanised.

The two existing answers each give up something important:

- **Verify the analyzer** (Verasco). Correct by construction, and a genuine masterpiece — but the analyzer is inside the trusted base, so its complexity is capped by what a team can prove. New analyses mean new proofs.
- **Verify the certificate** (proof-carrying code). The analyzer becomes untrusted and unbounded — but the certificate must be designed, and certificate design is where every practical attempt has stalled: too weak to express the invariants the analyzer finds, or too large to check in gatekeeper time.

CertCore is an attempt to make the second answer *reusable infrastructure* rather than a one-off prototype.

### 1.3 The LLM turn makes the second answer the only answer

As of 2026 the most interesting untrusted invariant generators are not hand-written fixpoint engines. They are language models and hybrid search procedures: excellent at proposing plausible invariants, structurally incapable of guaranteeing anything. You cannot "verify the analyzer" when the analyzer is a stochastic model with a vendor API. You *can* verify its output.

This is not a gimmick bolted onto the project; it is the reason the architecture matters now. A certificate kernel is the correct interface between a probabilistic reasoner and a trustworthy verdict. The kernel does not care whether the certificate came from a fixpoint iteration, a human, a SAT solver, or a language model — and that indifference is the whole point.

### 1.4 Why the time is right technically

- **Lean 4** now offers, in one toolchain: a small kernel, a real compiler, `#eval` for executable checkers, and enough of a standard library (`Array`, `Int`, `Rat`, `Json`) that a project like this needs *no* Mathlib. Ten years ago this project required Coq + extraction + OCaml plumbing and would have taken six months.
- **Trusted semantics for real languages now exist** — CompCert's C semantics, CN's separation-logic refinement types, CakeML's basis. A certificate kernel is only as useful as the semantics it certifies against; until recently there was nothing worth plugging into. CertCore starts on a toy language precisely because the *kernel* is the reusable part, and the plug-in point is now real (§16).
- **Certificate checking has been rehabilitated as a technique**: SMTCoq for SMT witnesses, verified LRAT checkers for SAT, Alive2 for compiler translation. The pattern is proven in adjacent areas and conspicuously absent for abstract interpretation.

---

## 2. Problem statement: why current solutions do not meet the requirement

### 2.1 Requirements

Six requirements define the target. They are not a wish list; each is derived from a concrete failure mode of an existing system.

| ID | Requirement | Derived from |
|---|---|---|
| **R1** | **Small, fixed TCB.** Safety rests on a kernel plus a small semantics; no solver, no elaborator, no analyzer in the trusted base. | Frama-C/WP, Liquid Haskell, Alive2 all trust an SMT solver; a solver bug is a soundness bug. |
| **R2** | **Analyzer is replaceable.** The guarantee survives replacing the analyzer with a buggy, heuristic, or ML-driven one. | Every "verified analyzer" (Verasco) binds soundness to one implementation. |
| **R3** | **Expressiveness beyond convex domains.** Non-convex, path-dependent invariants must be certifiable, not just discoverable. | Interval/octagon/polyhedra certificates are convex-only in practice; the analyzer finds disjunctive facts it cannot certify. |
| **R4** | **Gatekeeper cost.** Checking time linear-ish in program size; certificate size linear-ish and predictable; no certificate can induce super-linear work. | A checker that a hostile certificate can make run for hours is not a gate. |
| **R5** | **Extensible without re-proving the kernel.** A third party adds a domain or a precision mechanism and inherits soundness. | Verasco's domains are modular *internally*, but each new domain is a new proof obligation by the original authors. |
| **R6** | **Localised, machine-actionable rejection.** A rejected certificate names the program point, the edge, and the failed obligation. | The practical bottleneck in certifying workflows is the repair loop; also the interface an LLM needs. |

### 2.2 Where existing systems land

Ratings are coarse architectural judgements (● meets, ◐ partially, ○ does not), about *design*, not quality. All of these systems are excellent at what they were built for.
| System | R1 TCB | R2 replaceable | R3 non-convex | R4 cost | R5 extensible | R6 local |
|---|---|---|---|---|---|---|
| **Astrée** | ○ | ○ | ● | ● | ◐ | ◐ |
| **Verasco** | ● | ○ | ◐ | ◐ | ◐ | ○ |
| **Frama-C / WP + Why3** | ○ | ◐ | ● | ◐ | ○ | ● |
| **Liquid Haskell** | ○ | ○ | ◐ | ● | ○ | ● |
| **CN** | ◐ | ○ | ● | ◐ | ○ | ● |
| **VeriFast** | ○ | ○ | ● | ● | ○ | ● |
| **Alive2** (translation validation) | ○ | ◐ | ○ | ● | ○ | ◐ |
| **SMTCoq** | ● | ● | ○ | ● | ○ | ○ |
| **CertCore (target)** | ● | ● | ◐→● | ● | ● | ● |

The empty column-set is the point: **R1, R2, R5 and R6 have never been jointly satisfied**, and R3 is the thing everyone buys at the cost of one of them. SMTCoq has R1+R2 but no program invariants. Verasco has R1 but sacrifices R2 and R5. The SMT-backed tools have R3+R6 by trusting an oracle.

### 2.3 The gap, stated precisely

> There is no reusable, mechanically verified certificate infrastructure for abstract interpretation that (a) keeps the analyzer outside the trusted base, (b) composes across domains, and (c) admits path-sensitive invariants without abandoning linear-time checking.

### 2.4 The three technical obstacles

Any attempt to close that gap hits three specific problems. Naming them now makes the design in §4 auditable.

**O1 — Inclusion checking is where expressiveness dies.** A certificate is only as useful as the checker's ability to say "is abstract state `a` contained in abstract state `b`?" For intervals this is trivial. For octagons it is a closure computation with checkable witnesses. For polyhedra it is linear programming, rescued by Farkas certificates. For a *union* of convex sets — i.e. anything path-sensitive — inclusion becomes combinatorial (NP-hard in general), and the entire certifying approach seizes up. This is the single biggest reason certifying analysis stayed a prototype technique.

**O2 — Certificate size explodes faster than checker intelligence improves.** Necula's original experience: a minimal checker produced proofs ~1000× the code; a slightly smarter one got to ~2.5×. The ratio is a design variable with no theory behind it.

**O3 — Nobody writes the invariants.** Verification tools push the annotation burden onto humans (Frama-C, Dafny, Verus, Liquid Haskell). Analyzers push it onto heuristics that are then trusted. The certifying architecture makes a third option available — *any* generator, trusted or not — but only if the rejection signal is informative enough to drive a search loop.

---

## 3. Objectives and non-goals

### 3.1 Objectives

| ID | Objective | Measure of done |
|---|---|---|
| **O1** | A generic certificate kernel: one `check_sound` theorem, parameterised by a `CertDomain` structure. | Theorem closes with no `sorry`; `#print axioms` shows only Lean kernel axioms. |
| **O2** | Two verified combinators (product, reduced product) that transport certificate soundness. | Transfer theorems proved; checker instantiated for each; no new checker code per instance. |
| **O3** | Path sensitivity without a new certificate theory: finite-label product. | Simulation lemma + instantiation; benchmark cases where plain intervals fail and the labelled product succeeds. |
| **O4** | An untrusted Haskell analyzer producing certificates over a stable JSON wire format. | Analyzer is offline (no Lean dependency); protocol documented; corrupt certificates rejected. |
| **O5** | A measured expressiveness/cost frontier. | The north-star plot: safe-programs vs. cert bytes, across 2 domains × 3 partition depths, checker time flat. |

### 3.2 Non-goals (deliberate, not deferred-by-accident)

- **No C, no machine code, no floats.** The kernel is the deliverable; the language is a fixture.
- **No concurrency, no procedures, no heap.** Each would double the certificate theory; §16 sketches the path.
- **No automation of invariant discovery as a contribution.** The analyzer is a driver, not a research result. If it is good, that is a bonus, not a claim.
- **No claim of completeness.** The checker will reject some valid invariants (inclusion is not complete for octagons). This is documented, not fixed.
- **No head-to-head benchmark against Verasco/Astrée.** Infeasible for toolchain and language reasons; §13.4 explains what we measure instead and why that is honest.

---

## 4. Solution

### 4.1 Architecture

Two processes, one protocol, one theorem.

```
                        ┌─────────────────────────────────────────┐
   source .imp ──▶ parse ──▶ AST / CFG ──▶ AST.json            │
                        │  TRUSTED frontend (Lean)                │
                        └───────────────┬─────────────────────────┘
                                        │
                    ┌───────────────────▼───────────────────┐
                    │  UNTRUSTED  (Haskell)                 │
                    │  fixpoint engine + widening           │
                    │  + label instrumentation              │
                    │  emits  certificate.json              │
                    └───────────────────┬───────────────────┘
                                        │  JSON (untrusted input)
   ┌────────────────────────────────────▼────────────────────────────────────┐
   │  TRUSTED  (Lean 4)                                                      │
   │  decode ─▶ check_obligations ─▶ verdict                                 │
   │              │                                                          │
   │              ├─ init:      γ(entry) ⊇ Init                              │
   │              ├─ edges:     γ(transfer c (at p)) ⊆ γ(at q)               │
   │              └─ safety:    γ(at p) ⊆ SafePred(p)                        │
   │                                                                         │
   │  theorem: check_sound : check D p c = .ok → Safe p                      │
   └─────────────────────────────────────────────────────────────────────────┘
```

The trusted box contains: the JSON decoder + the checker + the semantics + the generic soundness proof. That is the entire TCB (modulo Lean's kernel and the C++ it compiles to — see §5 and §14).

### 4.2 The certificate kernel

The kernel's interface is a structure. Everything else is generic over it.

```lean
structure CertDomain where
  Abs            : Type
  gamma          : Abs → Set State            -- concretisation
  ble            : Abs → Abs → Bool            -- executable inclusion test
  ble_sound      : ∀ {a b}, ble a b = true → gamma a ⊆ gamma b
  top            : Abs
  top_sound      : ∀ s, s ∈ gamma top
  transfer       : Cmd → Abs → Abs
  transfer_sound : ∀ c {a s s'}, s ∈ gamma a → step c s = some s' →
                     s' ∈ gamma (transfer c a)
  join           : Abs → Abs → Abs
  join_sound     : gamma a ∪ gamma b ⊆ gamma (join a b)
```

Two design decisions carry the whole project:

1. **`ble` is `Bool`, `⊆` is `Prop`, and a reflection lemma bridges them.** The checker must *run*; the proofs must be *about* the real thing. This boundary is where most of the engineering time goes and it is the difference between a prototype and an artifact.
2. **The kernel never sees a fixpoint, a widening, or a heuristic.** It sees a map from program points to abstract states and checks that the map is *inductive*. The analyzer's cleverness is entirely outside the TCB — widening can be as unsound as it likes; a bad widening produces a certificate the checker rejects, not a wrong verdict.

Two-sided contract. Soundness alone is not enough; a checker that rejects everything is trivially sound:

```lean
theorem check_sound     : check D p c = .ok → Safe p
theorem encode_accepts  : IsPostFixpoint p I → check D p (encode p I) = .ok
```

`encode_accepts` is the theorem that makes the thing *usable*: every genuine inductive invariant has a certificate the checker accepts. Reviewers ask for it; most certifying prototypes cannot state it.

### 4.3 Combinators: certificates compose like domains

The kernel is only interesting if expressiveness can be added without touching it. There are two distinct mechanisms, and conflating them is a common design error.

**(a) Liftings that need no machinery at all.** Because `CertDomain` is a *structure* rather than a class hierarchy, a product domain is simply an instance: `Abs := Abs₁ × Abs₂`, componentwise `ble`, componentwise transfer — and the soundness fields are proved from the components' fields. There is no "combinator theorem" to state; the kernel's genericity does the work. This is the payoff of §4.2 and is worth demonstrating explicitly in the artifact.

**(b) Liftings whose certificate is *not* an abstract state.** This is where a real `Combinator` is needed:

```lean
-- A certificate encoding for a lifted domain
structure Encoding (D : CertDomain) where
  Cert    : Type
  decode  : Cert → (Lift D).Abs
  -- the checker validates the hints, not just the decoded state
  verify  : Cert → Bool
  -- the obligation: verify says yes ⇒ the decoded state is
  -- a genuine post-fixpoint of the lifted transfer
  verify_ok : verify c = true → IsPostFixpoint (Lift D) (decode c)
```

Two instances are in scope, one is a stretch:

- **Product.** `D₁ × D₂` with componentwise transfer and `ble`. Certificate = pair. Needs mechanism (a) only. Cheap, and it is the workhorse.
- **Reduced product.** Product plus a *reduction* `ρ : Abs₁ × Abs₂ → Abs₁ × Abs₂` that is sound (`γ(ρ(a,b)) ⊆ γ(a) ∩ γ(b)`) and idempotent (needed for the post-fixpoint check to close). This needs mechanism (b): the certificate must record *which* reductions fired, because the checker cannot recompute the fixpoint without replaying them. That recording is exactly the "hint" of Jensen–Pichardie, rediscovered in a typed setting — and the `verify_ok` obligation is where the intellectual risk lives (T7).
- **(Stretch) Disjunctive completion.** A genuine union domain with matching-based inclusion certificates. This is where O1 actually bites; see §7.5 for why it is a stretch and not a core claim.

### 4.4 Path sensitivity as a product, not a new theory

This is the conceptual move that makes R3 affordable.

The naive design says: "to certify a path-sensitive invariant, I need a disjunctive domain, and then my inclusion check is combinatorial." That is true and it is why the certifying approach died.

The alternative: **change the semantics, not the certificate theory.** Instrument the concrete semantics with a finite label `κ ∈ K` that is updated deterministically by each step (last branch taken; a bounded history; a predicate on the pre-state). Define the *label-instrumented* transfer on pairs `(Abs, K)` where `K` is the flat domain over a finite set. Then:

```
D_labelled  :=  D × Flat(K)
```

and path sensitivity is *derived* from the product combinator, with two obligations:

1. **Simulation.** The instrumented semantics does not change observable behaviour: `step# (s,κ) = some (s',κ') ↔ step s = some s'` (projection), and errors are preserved.
2. **Label adequacy.** The label determines the partition: `κ` is a function of the state alone (or of state + a finite history), so the pair `(abs-state, label)` is a sound abstraction of the concrete pair.

The payoff is architectural: **no new certificate theory, no new inclusion check, no new soundness proof per partition.** The cost is certificate size — the map now has `|Points| × |K|` entries (with sharing, closer to `|Points|` × the number of *reachable* labels). And that cost is precisely what the north-star experiment measures.

This is the honest form of the novelty: not "we invented partition certificates," but "we show that the thing everyone assumes needs a new theory is an *instance*, and we measure what it costs." That is a claim that survives review, because the proof is short and the measurement is the contribution.

### 4.5 The untrusted driver

A Haskell program that:

1. reads the AST as JSON from the trusted frontend and builds a CFG;
2. runs a chaotic-iteration fixpoint over `D` (interval, octagon) with standard widening;
3. optionally instruments labels to depth `k ∈ {0, 1, 2}`;
4. **verifies nothing** — it emits `certificate.json` and its own opinion;
5. on rejection, reads the checker's diagnostic and retries with a narrower certificate (drop a label, use a coarser state).

The driver is *deliberately* written in a different language from the checker. This is not a stylistic choice: it makes the TCB boundary architecturally real rather than a comment in a source file. If the two implementations of a transfer function disagree, the checker catches it — and the disagreement is itself data (see the differential test in §13.2).

### 4.6 Theorem inventory — the contract

This is what will actually be proven. Everything else is engineering.

| ID | Statement | Role | Difficulty |
|---|---|---|---|
| **T1** | `step_det : step c s = some s' → step c s = some s'' → s' = s''` | Semantics sanity | Low |
| **T2** | `safe_iff : Safe s ↔ ∀ n, run n s ≠ none` | Removes coinduction | Low |
| **T3** | `run_sound : s ∈ γ a → run n s = some s' → s' ∈ γ (transferStar n a)` | Lifts T-transfer to traces | Medium |
| **T4** | per-domain: `transfer_sound`, `join_sound`, `ble_sound` | Domain instances | Medium |
| **T5** | **`check_sound : check D p c = .ok → Safe p`** | **The kernel theorem** | **Medium** |
| **T6** | product instance: `ble_sound`, `transfer_sound`, `join_sound` for `D₁ × D₂` | Combinator (a) | Low |
| **T7** | **`reduce_sound : γ (ρ (a,b)) ⊆ γ a ∩ γ b`** + `reduce_idem` | **Reduced product** (the real one) | **High** |
| **T8** | `encode_accepts : IsPostFixpoint p I → check D p (encode p I) = .ok` | Usability / two-sidedness | Medium |
| **T9** | `label_sim : step# (s,κ) = some (s',κ') → step s = some s'` + converse | **Path sensitivity as product** | Medium |
| **T10** | `decode_sound : WellFormedCert c → ...` (malformed JSON ⇒ reject, never crash) | R4 / adversarial input | Low-Medium |

**The load-bearing three are T5, T7, T9.** T5 is the field's one-page induction and must be short — if it is not, the semantics is wrong for the purpose and no amount of proof effort fixes it. T7 is where the intellectual risk lives: a reduced product's reduction must be *sound* (easy to state, easy to get subtly wrong) and *idempotent* (often overlooked, and required for the post-fixpoint check to accept the fixpoint the analyzer actually computes). T9 is the quiet novelty.

T10 deserves a note: certifying analysis has an adversarial input model that verified analyzers do not. A malformed certificate must be rejected, not crash the checker, and must not be able to induce super-linear work. This is a *correctness* requirement on the decoder, and it is the kind of thing that gets skipped in research prototypes.

---

## 5. How the solution addresses each requirement

| Req | Mechanism | Why it works |
|---|---|---|
| **R1** | Analyzer is a separate process, unproven; TCB = kernel + semantics + decoder | `#print axioms` on `check_sound` is the audit; it names the kernel axioms and nothing else |
| **R2** | Architecture (B), not (A) | The theorem's statement does not mention any analyzer. Replacing the Haskell driver with a shell script changes nothing |
| **R3** | `D × Flat(K)` derived from the product combinator | No new inclusion check; the label is finite and flat, so inclusion is decidable and linear |
| **R4** | Cert size is `O(|Points| × |K|)`; each check is a `ble` call; decoder is total | No search in the checker at all — every obligation is decided by one `ble`. That is the strongest possible cost guarantee |
| **R5** | `CertDomain` interface + `Combinator` interface | A third party writes a structure instance; T5 instantiates at their domain without them touching the kernel proof |
| **R6** | `check` returns `Except Diagnostic` with `(point, edge, obligation, expected, actual)` | The diagnostic is a *first-class output*, not a string; the driver consumes it programmatically |

The R4 claim is worth stating plainly: **the checker performs no search.** Every obligation is a single decidable inclusion test between two abstract states. This is why checker time is linear and why it is predictable. It is also the design constraint that killed the disjunctive domain (matching is a search) and the reason §4.4 took the labelled-product route instead.

---

## 6. Differentiation from existing work

**Versus Verasco (POPL 2015).** Verasco is a *verified analyzer*: it proves that a particular fixpoint engine never lies. CertCore proves that a *checker* never lies, and consequently does not care what the engine is. Verasco's domains are modular but each new domain is a new proof by its authors; CertCore's `CertDomain` is a third-party extension point. Verasco has no diagnostic story; CertCore's rejection is the product. Verasco is the more impressive artifact; CertCore is the more *reusable* one. They are complementary, and CertCore's semantics are deliberately small enough to be replaced by CompCert's.

**Versus Jensen–Pichardie / TVS (TCS 2006).** This is the closest prior work and the honest baseline. They invented the certified-abstract-interpretation architecture and the fixpoint compression idea, with a paper metatheory and an unverified OCaml checker. CertCore is that idea *mechanised, generalised over domains, extended with combinators, and measured*. If CertCore has a single-sentence contribution, it is: *"we made the 2006 architecture into a verified toolkit and measured its frontier."*

**Versus Frama-C/WP, Dafny, Verus, Liquid Haskell, CN.** These verify programs against *human-supplied* specifications, and their automation rests on an SMT solver whose soundness is assumed. They are far more useful on real code today. CertCore differs on two axes: the invariants need not be human-supplied (only *certified*), and the TCB contains no solver. CN is the nearest neighbour among these — it already sends residual lemmas to Rocq — and the natural future is CertCore-as-a-CN-backend rather than CertCore-as-a-competitor.

**Versus SMTCoq.** Same architecture, different object: SMTCoq certifies *solver answers*; CertCore certifies *program invariants*. SMTCoq demonstrates that R1+R2 is achievable and practical; CertCore is the abstract-interpretation analogue.

**Versus Alive2 / translation validation.** Alive2 validates per-run compiler optimisations with bounded SMT checks. CertCore validates per-run *analyses* with unbounded, decidable checks. Both refuse to verify the tool; both check its output.

**Versus Astrée.** Astrée proves the point that abstract interpretation scales to avionics code; it does so with an unverified implementation and an informal soundness argument. CertCore trades Astrée's scale for a machine-checked verdict on a toy language. The interesting question — can the certificate approach ever reach Astrée's scale? — is exactly what §13's size measurements start to answer.

---

## 7. Novelty ledger, and what a reviewer will attack

Being precise about novelty is not modesty; it is the difference between a project that survives review and one that gets "this is just X + Y" and dies.

### 7.1 Borrowed (state it in the abstract, do not claim it)

- Proof-carrying code (Necula & Lee, POPL '97) and foundational PCC (Appel & Felty, POPL '00): the architecture.
- Certified abstract interpretation, fixpoint composition/hints (Besson–Jensen–Pichardie, TCS 2006): the certificate-as-post-fixpoint idea.
- Farkas certificates for polyhedra (Fouilhé–Monniaux–Périn, SAS 2013): the template for "certify an inclusion check."
- Trace partitioning (Mauborgne & Rival, POPL 2005): the idea that finite labels buy path sensitivity.
- Verasco's verified-domain architecture (POPL 2015): the `CertDomain` shape.
- Certifying algorithms (McConnell et al. 2011): the framing.

### 7.2 Engineering (valuable, not novel)

- Lean 4 mechanisation of the kernel and combinators.
- An executable, audited, dependency-free checker with a machine-checkable axiom footprint.
- A language-agnostic JSON certificate format with a total decoder.
- An untrusted Haskell driver with a repair loop.

### 7.3 Claims we will actually make

| # | Claim | Closest prior art | Status |
|---|---|---|---|
| **C1** | First *mechanised, domain-generic* certificate kernel for abstract interpretation with an executable checker and a two-sided theorem (soundness + acceptance-completeness). | TVS (unverified checker, paper metatheory); Verasco (verified analyzer, not certifying) | Defensible; verify by literature search in week 1 |
| **C2** | Verified *certificate combinators*: product and reduced product transport soundness, so expressiveness composes without touching the TCB. | Verasco composes *analyses*, not certificates | Defensible |
| **C3** | Path sensitivity is derivable as `D × Flat(K)` with a label-instrumented semantics — no new certificate theory, no combinatorial inclusion check. | Trace partitioning (unverified, analysis-side); disjunctive completion (analysis-side) | **Primary conceptual claim.** Modest but clean |
| **C4** | A measured precision/cost frontier for certifying analysis: safe-programs vs. certificate bytes across domain × partition depth, with checker time flat. | Anecdotes (Necula's 1000×→2.5×) but no systematic measurement that I know of | **Primary empirical claim.** This is the figure |
| **C5** | Diagnostic locality as a design objective, with a rejection format consumed programmatically by an untrusted generator. | PCC optimises size and checker intelligence, not repair ergonomics | Methodological; evaluated, not proven |

### 7.4 What a reviewer will say, and the answer

| Attack | Response |
|---|---|
| *"This is Verasco with extra steps."* | Verasco's theorem mentions its analyzer; ours does not (§4.2). Verasco's extension point is a new proof by the authors; ours is a structure instance (§4.3). The measurements do not exist in either. |
| *"Necula did this in 1997."* | Necula certified *types*; TCS 2006 certified *abstract interpretation* on paper with an OCaml checker. We mechanise, generalise, compose, and measure. The claim is C1–C5, not "PCC is new." |
| *"The label-product trick is obvious."* | Probably, in hindsight. The contribution is that it *works*, is proven (T9), and lets us replace an NP-hard check with a linear one — plus the measured price. "Obvious in hindsight, valuable to have established" is a legitimate genre. |
| *"Toy language, no floats, no concurrency — not useful."* | Correct, and deliberate (§3.2). The deliverable is a kernel, not a C tool. §16 states exactly what plugging into CompCert would require; claiming otherwise would be dishonest. |
| *"Reduced product was done in Verasco."* | Verasco verified the *analysis* reduction. We verify the *certificate* reduction, which additionally needs the reduction to be recorded, idempotent, and re-checkable (T7). Different theorem, same intuition. |
| *"Your evaluation has no baseline."* | True, and explained (§13.4). The alternative — a broken head-to-head against a 2015 Coq/CompCert toolchain on a different language — would be worse science. |
| *"A certificate checker in Lean is not fast enough to be a gatekeeper."* | This is the strongest attack. Mitigation: `ble` is `Bool`-valued and compiled; we report absolute times, and if they are bad we report that honestly as the paper's finding (that would itself be a result about the practical limits of the architecture). |

### 7.5 What we are *not* claiming, and the open problem we leave

We will not claim to solve disjunctive certificates. A genuine union domain needs a matching-based inclusion certificate, and the matching is a search — which violates R4 unless the search is bounded or the certificate is structured. §4.4 routes *around* the problem rather than through it: labels handle the common case (finite control-history partitions), and the combinatorial case remains open. This is stated up front because it is the first question a knowledgeable reader asks.

---

## 8. Scope

### 8.1 In scope

| Area | Content |
|---|---|
| **Language** | `Imp`: `skip`, assignment, sequencing, `if`, `while`, 1-D arrays (constant bounds), `assert`, integer division, signed 32-bit machine integers with overflow as a safety violation |
| **Semantics** | Fuel-indexed deterministic small-step; `none` = went wrong; `Safe s := ∀ n, run n s ≠ none` |
| **Properties** | no division by zero; array index in bounds; no signed overflow; user `assert`s hold |
| **Domains** | intervals (Int), octagons (difference bounds over Int), flat finite labels; product; reduced product |
| **Combinators** | product, reduced product (verified); label product (verified instance) |
| **Certificate** | JSON: entry state, sparse point→state map, per-edge successor labels, domain tag, format version |
| **Checker** | Lean 4, executable, total decoder, `Except Diagnostic` |
| **Analyzer** | Haskell: chaotic iteration + widening, label instrumentation depth 0/1/2, repair loop on rejection |
| **Benchmarks** | ~30 programs in 5 families (see §13.1) |
| **Evaluation** | precision vs. domain vs. depth; cert bytes; check time; mutation-fuzz rejection rate |

### 8.2 Out of scope (with the reason)

| Excluded | Why |
|---|---|
| C / machine code | Wrong month; the semantics would dominate. Plug point documented in §16 |
| Floating point | Verasco needed a thesis for this; it is not the kernel's problem |
| Procedures / recursion | Requires summaries and a compositional certificate theory — a second project |
| Heap / pointers | Requires a separation-logic certificate layer |
| Concurrency | Requires rely-guarantee certificates; the hardest open area |
| Disjunctive (matching-based) domain | Violates R4 as designed; see §7.5 |
| Invariant *inference* quality | The driver is a fixture, not a contribution |
| Completeness of inclusion for octagons | Documented limitation, not a bug |

### 8.3 The precision ladder (how scope can shrink without failing)

The design is layered so that running out of time degrades gracefully:

1. **L0 (must):** intervals + generic kernel + check_sound + Haskell driver. *This alone is a complete, defensible artifact.*
2. **L1 (should):** + product combinator + octagons.
3. **L2 (should):** + label product + T9 + the north-star plot.
4. **L3 (nice):** + reduced product with hints + T7.
5. **L4 (stretch):** + disjunctive matching certificates, or an LLM producer, or a CN/CompCert plug-in sketch.

Shipping L1 is success. L3 is a strong month.

---

## 9. How it could be used

- **U1 — Certifying a third-party analyzer.** A vendor's analyzer emits CertCore certificates alongside its verdicts; a customer's build checks them against a semantics they trust. The vendor keeps their proprietary engine; the customer stops taking it on faith. This is the commercial shape of PCC and it has never had a reusable kernel underneath it.
- **U2 — A trustworthy oracle for AI agents.** An agent (or a swarm, or a human) proposes invariants; CertCore disposes. The rejection diagnostic is the feedback channel, and it is a *typed* object rather than a sentence, which is what makes the loop programmable. This is the most likely near-term use and the reason R6 is a requirement rather than a nicety.
- **U3 — A CI gate with an auditable TCB.** Certificates checked in the build; the TCB fits in a page of audit; the axiom footprint is one command. For safety-critical suppliers who must justify their toolchain (DO-178C-style arguments), "our analysis is certified by a checker whose soundness is machine-checked" is a qualitatively different sentence from "we use a sound tool."
- **U4 — An arbiter between disagreeing analyzers.** If analyzer A says safe and B says unsafe, whoever can produce a certificate wins. The checker settles disputes that are currently settled by reputation. (This is a genuinely under-exploited idea, and it costs almost nothing once certificates exist.)
- **U5 — A teaching artifact.** The whole architecture fits in a course: semantics, abstract interpretation, proof, TCB, adversarial input. The corrupt-a-certificate demo (§12.7) is the best 90 seconds in the subject.
- **U6 — A certificate *format* under a proof-assistant frontend.** Because the checker *is* Lean, acceptance is already a kernel-checked fact; emitting a readable proof script from the same certificate is a short step. The certificate becomes the interchange format between automated analysis and interactive proof.
- **U7 — A target for compilation-verified pipelines.** CompCert certifies "the compiler preserves behaviour"; CertCore certifies "this behaviour is safe." Composed, they give source-to-binary safety with two independent, small TCBs.

---

## 10. Pipeline

### 10.1 Runtime pipeline (per program)

| Stage | Component | Trusted? | Failure mode |
|---|---|---|---|
| 1. Lex/parse | Lean frontend (D5) | **Yes** | reject |
| 2. CFG / AST | Lean | **Yes** | reject |
| 3. Analysis | Haskell fixpoint + widening | No | may produce no certificate |
| 4. Instrument labels | Haskell | No | — |
| 5. Encode certificate | Haskell | No | malformed JSON |
| 6. Decode | Lean, total | **Yes** | `Diagnostic.malformed` |
| 7. Check obligations | Lean, `ble` only | **Yes** | `Diagnostic.edge …` |
| 8. Verdict | Lean | **Yes** | safe / unsafe / malformed |
| 9. Repair (optional) | Haskell reads diagnostic | No | give up |

Note stage 1: the frontend is in the TCB whichever language it is written in, because a parser bug changes what "safe" means. For a month we keep the frontend in **Lean** so that the TCB is one language and one reviewable file, and the Haskell side receives an already-parsed AST in JSON. This is a deliberate TCB-shrinking choice (§11, D5).

### 10.2 Verification pipeline (per commit)

```
lake build            # proofs + checker; fails on sorry
lean --run audits    # #print axioms check_sound → must be {propext, Quot.sound} only
stack build           # Haskell analyzer
golden tests          # 30 programs × expected verdicts
mutation fuzz         # 10k mutated certificates; zero accepts
bench                 # precision + size + time → CSV → plot
```

### 10.3 Certificate wire format (sketch)

```json
{
  "format": "certcore/1",
  "program_hash": "…",
  "domain": {"kind": "product", "left": "interval", "right": "octagon"},
  "labels": {"kind": "flat", "size": 4, "description": "last-branch, depth 2"},
  "entry": { "point": 0, "state": { … } },
  "states": [ { "point": 3, "label": 1, "state": { … } }, … ],
  "successors": [ { "from": 3, "label": 1, "cmd": 7, "to": [4,2], "labels": [1,3] } ],
  "assertions": [ { "point": 9, "state": { … }, "predicate": "index_in_bounds" } ]
}
```

Two format decisions: **human-readable** (JSON, not a binary blob) because debuggability *is* a design goal here (R6), and **hash-pinned to the program** so a certificate cannot be silently transplanted.

---

## 11. Tech stack and decision justifications

| # | Decision | Alternatives rejected | Justification |
|---|---|---|---|
| **D1** | **Lean 4** for proofs and checker | Rocq/Coq, Isabelle, Agda, F\* | Lean 4 gives a *small kernel* and an *executable checker in the same file as its proof*: `#eval check p c` next to `theorem check_sound`. Rocq would need extraction + OCaml plumbing for the checker (more moving parts in the TCB), and its JSON story is worse. Agda has no compiler-grade execution story. F\* would put an SMT solver back in the TCB, defeating R1. Lean's `#print axioms` also gives a one-command audit, which is a deliverable (§14). |
| **D2** | **No Mathlib** | Mathlib, `Std` only | Our mathematics is elementary: `Int`, `Rat`, `Array`, `List`. Mathlib would add ~a million lines, multi-minute builds, and version churn, for lemmas we can write in a day. It also muddies the TCB story: the kernel is the kernel either way, but "no dependencies" is auditable and reproducible. Risk (missing list lemmas) mitigated by a local `Lemmas.lean`. |
| **D3** | **Haskell** for the untrusted analyzer | Lean, OCaml, Python, Rust | Three reasons. (i) It makes the TCB boundary *architectural*: two languages, one wire format, no accidental trust. (ii) The driver is a fixpoint engine over a lattice — Haskell's type classes and `Data.Map` express that cleanly, and `aeson` gives the JSON. (iii) It plays to the author's strengths, which matters in a four-week sprint. Python was tempting (fastest to write) but would have made the boundary look like a script; OCaml is Verasco's extraction target and would invite "so it's Verasco." **Fallback:** a Lean-side reference driver if the JSON plumbing overruns (see R3 in §12.6) — the architecture survives, the boundary claim weakens. |
| **D4** | **JSON** wire format | S-expressions, Protobuf, CBOR, custom text | S-expressions are Lean-native and prettier to a PL person, but LLM producers and third-party tools speak JSON. Protobuf/CBOR are compact but opaque, adding a codegen step and a decoder in the TCB. JSON is verbose — and that verbosity is *the measured cost* in C4, so it must not be hidden. Also: a human can read a rejected certificate and see the bug. |
| **D5** | **Frontend in Lean**, analyzer consumes AST-as-JSON | Frontend in Haskell | The parser is in the TCB no matter where it lives. Keeping it in Lean means the TCB is one language, one build, one audit. It also guarantees the analyzer and checker agree on what the program *is* — the one thing a differential test cannot catch. |
| **D6** | **Fuel-indexed deterministic semantics** | Relational big-step, coinductive `Safe`, step-indexed | Avoids coinduction and termination side conditions entirely; `Safe s := ∀ n, run n s ≠ none` is honest (infinite loops are safe because every finite prefix is) and makes T2/T3 ordinary inductions. A relational semantics would be more faithful to the literature but would cost a week of proof plumbing for no added assurance at this scale. |
| **D7** | **`ble : Bool` + reflection lemma** (not `Decidable` typeclass everywhere) | `Decidable` everywhere, `Prop`-only with `decide` | The checker must be *compiled and fast*; `Decidable` instances are convenient but their reduction behaviour under `#eval` is less predictable and they encourage expensive `decide` calls in the checker. An explicit `Bool` function plus a `ble_sound` lemma is duller, faster, and gives a clean cost model. |
| **D8** | **Lake + pinned `lean-toolchain` + `lake-manifest.json`** | Nix, Docker, "latest" | Reproducibility for an artifact that will be evaluated by strangers; Lake is the native tool and adds nothing to the TCB. Nix is better in principle and would cost a day to set up; a pinned toolchain plus a short README gets 90% of the benefit. |
| **D9** | **Python** for the benchmark/fuzz harness | Haskell, shell, Lean | The harness is not part of the artifact's correctness story; Python + `json` + `random` writes a certificate mutator in an hour. Using Haskell here would tempt code sharing with the analyzer and blur the boundary. |
| **D10** | **`#print axioms` as a CI gate** | Trust the proof | A `sorry` or an accidental `Classical.choice` is a silent soundness hole. A CI step that greps the axiom footprint of `check_sound` is ten lines and is the strongest guarantee in the repo. |

---

## 12. Plan

### 12.1 Week 0 (2 days, before the clock starts)

- Freeze the language grammar, the semantics signature, and the JSON schema (v1). **The schema is the interface; changing it in week 3 costs a day.**
- Write `THEOREMS.md` (the T-names and statements) and `NONGOALS.md`.
- Literature check for C1 (an afternoon of searching for "certified abstract interpretation" + "verified checker" + "certificate combinators"). If someone has already done the kernel, reposition to C3+C4 and cite them.
- Set up repo, Lean toolchain, CI, benchmark harness skeleton.

### 12.2 Week 1 — Semantics and the kernel

| Day | Work |
|---|---|
| 1 | AST, CFG, fuel semantics, `Safe`, T1, T2 |
| 2 | Interval domain, `gamma`, `ble`, `transfer`, T4 (intervals only) |
| 3 | **T5 `check_sound`** — get it closed on intervals, however ugly |
| 4 | T3 (trace soundness), `encode` + T8, `Diagnostic` type |
| 5 | T10 (total decoder), golden tests, first end-to-end run |

**Gate G1 (end of week 1):** `lake build` clean, one program verified end-to-end via a hand-written certificate, `#print axioms` clean. *If T5 is not closed by day 5, cut octagons and reduced product permanently and go all-in on the driver and measurements.*

### 12.3 Week 2 — Combinators and the driver

| Day | Work |
|---|---|
| 6 | Haskell frontend client + AST JSON + fixpoint engine over intervals |
| 7 | Certificate encoder + repair loop on `Diagnostic` |
| 8 | Product combinator, T6; instantiate checker for products |
| 9 | **Reduced product** `ρ`, T7 (`reduce_sound`, `reduce_idem`), hints in the certificate |
| 10 | Octagon domain (closure, witness paths), T4 for octagons |

**Gate G2 (end of week 2):** the Haskell analyzer verifies ≥ 10 programs end-to-end through the Lean checker; corrupted certificates are rejected. *If G2 is at risk, drop octagons (keep intervals only) — the plot still works with depth as the second axis.*

### 12.4 Week 3 — Path sensitivity and the frontier

| Day | Work |
|---|---|
| 11 | Label instrumentation, T9 (`label_sim`), flat-label domain |
| 12 | Label product instantiation; depth 0/1/2 in the driver |
| 13 | Benchmark suite complete (~30 programs, 5 families) |
| 14 | **Run the experiment**: precision × domain × depth; record cert bytes, check time, analyzer time |
| 15 | The north-star plot; identify the failures (programs no depth can certify) |

**Gate G3 (end of week 3):** the plot exists and is not embarrassing. *This is the kill criterion for the empirical claim C4: if certificate size explodes super-linearly before precision improves, report that — it is a real finding about the architecture and it belongs in the write-up.*

### 12.5 Week 4 — Hardening, writing, artifact

| Day | Work |
|---|---|
| 16 | Mutation fuzz (10k certs, zero accepts); adversarial decoder tests |
| 17 | Performance pass; `ble` optimisation; measure absolute check times |
| 18 | Repo hygiene: README, `THEOREMS.md`, `TCB.md`, demo script, asciinema |
| 19 | Write-up (8 pages: problem, design, T5/T7/T9, measurements, threats) |
| 20 | Buffer / overflow |

### 12.6 Risk register

| # | Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|---|
| R1 | T7 (reduced product) doesn't close — reduction not idempotent or hint recording insufficient | Medium | High | Gate G1 drops it; product alone satisfies O2; T7 is L3 |
| R2 | Lean checker is too slow to be a credible gatekeeper | Medium | High | Report honestly as a finding; optimise `ble` with `UInt64`; the claim becomes "here is where it breaks" |
| R3 | Haskell ↔ Lean JSON plumbing overruns | Medium | Medium | Fallback: Lean reference driver (keeps O1–O3, weakens C2's boundary claim) |
| R4 | Certificate size explodes, plot is useless | Medium | Medium | It is a *result* if reported well; add sharing/delta encoding as a day's work |
| R5 | Octagon closure proof is fiddly | High | Medium | Intervals + labels already show the frontier; octagons are L1 |
| R6 | Someone has already published C1 | Low-Med | High | Week-0 literature check; reposition to C3+C4 |
| R7 | Scope creep toward real C | High | High | `NONGOALS.md`, and the gate structure |
| R8 | Time lost to Lean metaprogramming temptation | Medium | Medium | No macros in the kernel; hand-write the boring parts |

### 12.7 Demo (the 3-minute version)

1. `certcore analyze examples/div.imp` → the analyzer claims **safe** and prints a certificate.
2. `certcore check examples/div.imp cert.json` → **ACCEPT** (`#print axioms` shown alongside).
3. Mutate one byte of the certificate (flip a bound) → **REJECT**, with `Diagnostic.edge point=7 expected=[0,10] actual=[0,12]`.
4. Show the 4-line theorem that makes step 2 mean something.
5. Show the plot: precision bought with bytes; checker time flat.

Step 3 is the emotional core: the checker catches a **lie**, in public, in milliseconds.

---

## 13. Evaluation

### 13.1 Benchmark families (~30 programs)

| Family | n | Purpose |
|---|---|---|
| Straight-line arithmetic | 6 | Baseline; overflow cases |
| Loops needing widening | 6 | Where intervals lose precision |
| Array bounds | 6 | The classic safety property |
| Path-sensitive (intervals provably fail; labels win) | 8 | The C3/C4 experiment |
| Small realistic kernels (binary search, bubble sort, string copy, gcd) | 4 | Plausibility |

### 13.2 Metrics

- **Precision:** programs proven safe, per (domain × depth). Report *both* directions: safe-proven, and unsafe-detected (with a certificate of *unsafety*? — out of scope; note as limitation).
- **Cost:** certificate bytes; checker wall time; analyzer wall time; ratio check/analyze.
- **Robustness:** mutation-fuzz acceptance rate (target: 0/10,000); malformed-JSON crash rate (target: 0).
- **Agreement:** differential test of Haskell vs. Lean transfer functions over randomly generated states — disagreements are bugs in one of them, and the checker is the arbiter.

### 13.3 Targets (not guarantees)

- checker ≤ 1,500 lines of Lean, excluding semantics;
- cert ≤ 20× source bytes at depth 2;
- check time ≤ 5% of analyze time;
- ≥ 25/30 programs certified at some depth;
- 0 accepts over 10k mutations.

### 13.4 Threats to validity — stated in advance

1. **Toy language.** Nothing here transfers to C *without* replacing the semantics. The kernel transfers; the numbers do not.
2. **No baseline.** We cannot run Verasco (2015 Coq/CompCert, different language) and will not fake a comparison. We measure within-system properties and architectural claims instead, and say so.
3. **Small benchmarks.** Thirty programs cannot establish scalability. They can establish *shape* (linear vs. not), which is what the plot needs.
4. **Author-designed benchmarks.** Risk of cherry-picking. Mitigation: publish the whole suite including the failures, and report programs that *no* configuration certifies.
5. **The driver is ours.** Precision numbers measure our driver as much as the kernel. Mitigation: report certificate-size for the *same* invariant set across depths, which isolates the encoding cost from the inference quality.

---

## 14. Definition of done

- [ ] `lake build` succeeds with **zero `sorry`** in the trusted tree.
- [ ] `#print axioms check_sound` reports only `propext` and `Quot.sound` (or fewer); CI-enforced.
- [ ] T1–T6, T8–T10 closed; T7 closed or explicitly documented as dropped at L2.
- [ ] Haskell analyzer certifies ≥ 25/30 benchmarks through the Lean checker.
- [ ] 10,000 mutated certificates, zero accepted, zero crashes.
- [ ] The north-star plot, with raw CSV checked in.
- [ ] `TCB.md`: one page listing every trusted component and why.
- [ ] `THEOREMS.md`: every theorem with its statement and status.
- [ ] Demo script runs in ≤ 3 minutes from a clean clone.
- [ ] Write-up: 8 pages, including a threats-to-validity section that is not a formality.

---

## 15. Deliverables and repository layout

```
certcore/
  lean/
    CertCore/Semantics.lean      -- AST, step, run, Safe            [TCB]
    CertCore/Domain.lean         -- CertDomain, Combinator          [TCB]
    CertCore/Domain/Interval.lean
    CertCore/Domain/Octagon.lean
    CertCore/Domain/Label.lean
    CertCore/Domain/Reduce.lean  -- reduced product
    CertCore/Cert.lean           -- certificate type, encode/decode [TCB]
    CertCore/Check.lean          -- the checker                    [TCB]
    CertCore/Proofs.lean         -- T1..T10
    CertCore/Audit.lean          -- #print axioms
  haskell/
    src/Analyze.hs            -- untrusted fixpoint engine
    src/Emit.hs               -- certificate encoding
    src/Repair.hs             -- diagnostic-driven retry
  examples/                   -- 30 .imp programs
  bench/                      -- harness, mutation fuzzer, plotting
  docs/                       -- TCB.md, THEOREMS.md, paper.pdf, demo.md
```

---

## 16. After the month

- **Workshop paper** (CPP / ITP / SAS short): the kernel + the frontier plot. C1–C4 is a credible short paper.
- **Artifact evaluation**: the repo is already shaped for it (pinned toolchain, demo script, CI).
- **Roadmap, in order of value-per-effort:** (1) an LLM producer on the same JSON interface — cheap, timely, and directly tests R6; (2) function summaries as certificates — the first real compositional step; (3) plug into CN's residual-lemma export — the path to real C without redoing the semantics; (4) a disjunctive matching certificate with a bounded search — the open problem of §7.5; (5) CompCert Clight semantics as the trusted layer.

---

## 17. If you only take one thing from this plan

The design is one sentence: **move every source of cleverness outside the trusted base, and make the certificate the only interface.**

That sentence explains the language split (D3), the refusal to verify the analyzer (R2), the derivation of path sensitivity as a product rather than a new domain (§4.4), the absence of search in the checker (R4), and the deliverable being a plot rather than a tool (C4). Everything else is a consequence.

---

## Appendix A — References

1. G. Necula, P. Lee. *Proof-Carrying Code.* POPL '97.
2. G. Necula, P. Lee. *[The Design and Implementation of a Certifying Compiler.](http://www.cs.cmu.edu/Groups/fox/papers/necula-pldi98.abstract)* PLDI '98.
3. A. Appel, A. Felty. *[A Semantic Model of Types and Machine Instructions for Proof-Carrying Code.](https://dl.acm.org/doi/abs/10.1145/325694.325727)* POPL 2000.
4. F. Besson, T. Jensen, D. Pichardie. *[Proof-Carrying Code from Certified Abstract Interpretation and Fixpoint Compression.](https://dlnext.acm.org/doi/10.1016/j.tcs.2006.08.012)* TCS 364(3), 2006.
5. J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy, D. Pichardie. *[A Formally-Verified C Static Analyzer.](https://dl.acm.org/doi/abs/10.1145/2676726.2676966)* POPL 2015.
6. A. Fouilhé, D. Monniaux, M. Périn. *[Efficient Generation of Correctness Certificates for the Abstract Domain of Polyhedra.](https://hal.halpreprod.archives-ouvertes.fr/hal-00806990v1)* SAS 2013.
7. L. Mauborgne, X. Rival. *Trace Partitioning in Abstract Interpretation Based Static Analyzers.* ESOP 2005.
8. A. Pnueli, M. Siegel, E. Singerman. *[Translation Validation.](https://weizmann.elsevierpure.com/en/publications/translation-validation-2/)* TACAS '98.
9. C. Pulte et al. *[CN: Verifying Systems C Code with Separation-Logic Refinement Types.](http://algo.cs.ox.ac.uk/people/christopher.pulte/popl23.html)* POPL 2023.
10. [SMTCoq](https://github.com/smtcoq/smtcoq) — certified checking of SAT/SMT witnesses in Coq.
11. [Alive2](https://m2.mtmt.hu/api/publication/33403789) — bounded translation validation for LLVM.
12. D. Bjørner, et al. — certifying algorithms survey: McConnell, Mehlhorn, Näher, Schweitzer. *Certifying Algorithms.* Computer Science Review, 2011.
13. P. Cousot. *[The Astrée Static Analysis Tool](https://cs.nyu.edu/~pcousot/publications.www/slides/Cousot-07-10-16_17-ESPASS_4-1-lg.pdf)* (slides) — the "before" picture.
