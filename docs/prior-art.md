# Prior art — the M0.6 check for C1

| | |
|---|---|
| Date | 2026-11-21 |
| Trigger | Roadmap M0.6: search "certified abstract interpretation" + "verified certificate checker"; reposition claims if the space is occupied |
| Method | Web search across arXiv, ACM DL, HAL, zbMATH, conference pages; abstracts and metadata read, most full texts paywalled |
| Outcome | **Claims C1–C3 need rewording before the write-up. C4 survives.** One factual error in the plan must be corrected (§2) |

## 1. Bottom line

| Claim | Status | What actually survives |
|---|---|---|
| **C1** — first mechanised, domain-generic certificate kernel with executable checker and two-sided theorem | **Partially occupied** | Not "first mechanised checker" (2006) and not "first domain-generic mechanised AI" (Verasco 2015). Survives only as: *one fixed executable checker, parametric in a `CertDomain` structure, with a mechanised acceptance-completeness theorem* |
| **C2** — verified certificate combinators transport soundness without touching the TCB | **Partially occupied** | Product/reduced-product soundness is mechanised at the *analyzer* level (Verasco functors, Blazy et al. SAS 2013, ICFP 2024, Rocq Bottom 2026). Survives as *certificate-level* transport: the combinator acts on certificates, not analyses |
| **C3** — path sensitivity is a product, not a new certificate theory | **Theory occupied; mechanised certifying instance not found** | Trace partitioning is the established construction and is explicitly a domain *combiner*. Reword from "we show it is an instance" (a corollary others could have drawn) to "first mechanised, certifying instance, with no change to the certificate format" |
| **C4** — measured precision/cost frontier | **Survives as data, not as capability** | Compressed certificates, certification overhead and validation times have all been measured before. What is new is the *systematic frontier across domain × depth*. State it against Keel's proved linear bounds, not just observed flatness |

## 2. The plan is wrong about its closest predecessor — fix this first

Plan §6 says Besson–Jensen–Pichardie (TCS 2006) had "a paper metatheory and an
**unverified OCaml checker**", and §7.4 repeats it in the reviewer Q&A. That
characterisation does not match the published record. The paper's abstract
states that "proof checkers carry their own correctness proofs and accepting a
new proof checker amounts to **type checking the checker in Coq**", and the
same group describes having "formalised the theory of abstract interpretation
inside the proof assistant Coq and **extracted Caml implementations**".

So the 2006 architecture already had: an untrusted producer, a compact
certificate, a machine-checked checker admitted by type-checking, and an
extensibility story. Correcting this is not cosmetic — it is what removes
"first mechanised" from C1. The delta that remains is real but narrower:
Besson et al. admit a new domain by *shipping a new checker and proving it*;
CertCore has **one fixed checker program** whose parameter is a structure with
proof fields, so a new domain is a structure instance and the kernel proof is
never re-run. That is the claim to defend.

**Before asserting it, get the full text** and check whether they prove an
acceptance-completeness result. If they do, C1 collapses to "Lean 4 + one fixed
parametric checker + the measured frontier", and the write-up must say so.

## 3. Closest works

| Work | Venue | Why it matters here |
|---|---|---|
| Besson, Jensen, Pichardie, *Proof-Carrying Code from Certified Abstract Interpretation and Fixpoint Compression* | TCS 364(3), 2006 | The closest preemption of C1: untrusted producer, compact certificates ("strategies for reconstructing a fixpoint"), Coq-certified extracted checker, new domains admitted by type-checking |
| Besson, Jensen, Pichardie, Turpin, *Certified result checking for polyhedral analysis of bytecode programs* | TGC 2010 | Coq-certified checker consuming Farkas/linear-combination witnesses — preempts "small verified checker + per-operation certificates" for one domain |
| Wildmoser, Chaieb, Nipkow, *Bytecode Analysis for Proof Carrying Code* | ENTCS 2005 | Isabelle/HOL VC generator checks untrusted interval annotations; the trusted/untrusted composition idea, a decade early |
| Jourdan, Laporte, Blazy, Leroy, Pichardie, *A Formally-Verified C Static Analyzer* (Verasco) | POPL 2015 | Mechanised, domain-generic AI with an explicit domain interface — but verifies the *analyzer*, not a checker |
| Blazy, Laporte, Maroneze, Pichardie, *Formal Verification of a C Value Analysis Based on Abstract Interpretation* | SAS 2013 | Coq domain functors including a direct product whose concretisation is the intersection — mechanised product combinator, analyzer side |
| Michelland, Zakowski, Gonnord, *Abstract Interpreters: A Monadic Approach to Modular Verification* | ICFP 2024 | Generic combinators proved once, soundness lifted generically — preempts "verified combinators" as a novelty |
| Lemerre, *Rocq Bottom: Beyond Soundness with Precise Reasoning about Analysis Precision* | SAS 2026 | Domain-generic Rocq library with combinators composing *precision*; the most dangerous 2026 item for C2 and for the γ-only interface being presented as an insight |
| Mauborgne, Rival, *Trace Partitioning in Abstract Interpretation Based Static Analyzers*; Rival, Mauborgne, *The trace partitioning abstract domain* | ESOP 2005; TOPLAS 2007 | Occupies C3's theory: partitioning is a parameterised domain combined with the underlying one — a textbook instance of `D × Flat(K)` |
| Fouilhé, Monniaux, Périn, *Efficient Generation of Correctness Certificates for the Abstract Domain of Polyhedra* | SAS 2013 | Untrusted oracle emits Farkas certificates for a much smaller proved checker — preempts per-operation certificate design |
| Boulmé, Maréchal, Périn, *Refinement to Certify Abstract Interpretations, Illustrated on Linearization for Polyhedra* | JAR 2019 | Certifies computations on abstract domains independently of the domain implementation |
| Trabish, Itzhaky, *Enhancing Symbolic Execution with Machine-Checked Safety Proofs* | CPP 2026 | Untrusted KLEE emits Coq-checked safety proofs with measured validation times — CertCore's architecture, different analysis |
| Cai, Chang, Nagarakatte, *Keel: A Verified In-Kernel Proof Checker for Proof Carrying BPF* | arXiv 2611.11117, Nov 2026 | Lean 4 verified certificate checker against bit-vector semantics, with a C refinement proof and **proved linear time/memory bounds** — removes "first Lean 4 verified certificate checker" and sets the complexity bar |
| McConnell, Mehlhorn, Näher, Schweitzer, *Certifying algorithms* | Computer Science Review, 2011 | The output-plus-witness-plus-checker contract, including the completeness half — so `encode_accepts` is the standard contract applied to AI |

## 4. Claim by claim

### C1 — narrow it to the fixed-checker property

- **Do not say** "first mechanised certificate checker for abstract
  interpretation" (false, 2006), "first domain-generic mechanised AI" (false,
  Verasco 2015), or "first Lean 4 verified checker" (false — Keel, LeanVIPR,
  LeanSAT, cache_lpr).
- **Say** "to our knowledge, the first certificate kernel for abstract
  interpretation in which a single executable checker is parametric in a domain
  structure, together with a mechanised acceptance-completeness theorem".
- **Then define "kernel" operationally** (one fixed program; domain proofs are
  parameters; no per-domain checker code) and put a date-stamped comparison
  table against TCS 2006, TGC 2010, Verasco, Rocq Bottom, Keel, CPP 2026.
- **The honest TCB caveat:** `check_sound` takes the domain's soundness proofs
  as parameters, so those proofs sit inside the trusted base just as an
  extracted per-domain checker does. The difference is *proof term checked by
  the kernel* versus *checker code checked by the kernel* — a difference in
  shape and ergonomics, not a strictly smaller TCB. Say that before a reviewer
  does.

### C2 — transfer, not composition

Product and reduced product soundness are already mechanised in Coq at the
analyzer level. The defensible delta is that CertCore's combinators transport
*soundness of certificates* — the object being composed is a certificate, not an
analysis — and that the checker does not change. Keep M6's "zero lines changed
in `Check.lean`" as the evidence and cite Blazy et al. and ICFP 2024.

### C3 — a corollary, not a discovery

Trace partitioning already is "a product of the base domain with a finite label
domain"; the plan's framing ("we show that the thing everyone assumes needs a
new theory is an instance") overstates novelty. The value is the *mechanised,
certifying* instance: no new certificate theory, no combinatorial inclusion
check, and a measured byte cost. Reword, cite ESOP 2005 / TOPLAS 2007 / Rival's
thesis, and let the proof and the measurement carry the claim.

### C4 — the strongest surviving claim

Nothing found systematically measures safe-programs vs certificate bytes across
domain × partition depth with checker time overlaid. Keep it, but:

- state it as *data*, not as a new capability;
- measure against Keel's proved linear bounds, and against the 2006 fixpoint
  compression numbers, so "flat" means something;
- report absolute times, as the plan already promises.

## 5. Concurrent 2026 work to cite and differentiate

- **Keel** (Nov 2026) — Lean 4, verified, linear-time checker for eBPF. Closest
  modern architecture; different object (bit-vector verifier certificates, not
  domain-generic inductive invariants).
- **LeanVIPR** (NeurIPS 2026) — VIPR MIP-certificate checker in Lean 4.
- **LeanMVerify** (Zenodo 2026) — single-author Lean 4 artifact: fuelled
  IMP-with-pointers semantics and a proof-producing abstract interpreter.
  Unrefereed; no two-sided theorem found. Cite as concurrent, not established.
- **Rocq Bottom** (SAS 2026) — domain-generic verified AI library with precision
  combinators.
- **Basis, "Ship Your Interpreter"** (Oct 2026) — Lean 4 interpreted-language
  semantics plus a sound abstract interpreter in days. Removes any "first Lean 4
  AI formalisation" framing.
- **Goblint Validator** (TACAS 2024) — AI-based witness validation at SV-COMP
  scale; the unverified empirical baseline for C4.

## 6. What must be checked before the abstract is written

1. **Besson et al. TCS 2006, full text**: is there an acceptance/completeness
   theorem? Is their checker a functor over a domain signature or duplicated per
   domain? Everything in C1 turns on these two answers.
2. **Verasco's reduction**: generic functor or hand-written per pair of domains?
3. **Rocq Bottom**: does it include any certificate or checker notion?
4. **LeanMVerify**: actual theorem statements.
5. **SAS/VMCAI/ITP 2026 tables of contents**: the search was opportunistic, not
   systematic. A Lean 4 AI certificate kernel could exist in a venue or
   repository this pass missed.

## 7. Proposed amendments (for review — not yet applied)

| Where | Change |
|---|---|
| Plan §6, TCS 2006 paragraph | Replace "unverified OCaml checker" with "Coq-certified checkers, admitted by type-checking" |
| Plan §7.3 C1 | Reword to the fixed-checker + acceptance-completeness version |
| Plan §7.3 C2 | Add "certificate-level, not analysis-level" |
| Plan §7.3 C3 | Reword to "first mechanised, certifying instance of trace partitioning" |
| Plan §7.4 | Replace the "Necula did this in 1997" answer with the 2006 comparison |

Applying these is M12 work (the write-up), not M0; recorded here so the
correction is not lost.

## 8. References

Verified during this pass (page opened):

- Keel — <https://arxiv.org/abs/2611.11117>
- TCS 2006 DOI — <https://doi.org/10.1016/j.tcs.2006.08.012>
- Verasco — <https://dl.acm.org/doi/abs/10.1145/2676726.2676966>
- Blazy et al. SAS 2013 — <https://ar5iv.labs.arxiv.org/html/1304.3596>
- Farkas certificates — <https://hal.science/hal-00806990>
- Trace partitioning ESOP 2005 — <https://dl.acm.org/doi/abs/10.1007/978-3-540-31987-0_2>
- Certifying algorithms — <https://dl.acm.org/doi/abs/10.1016/j.cosrev.2010.09.009>
- Necula & Lee, POPL 1997 — <https://doi.org/10.1145/263699.263712>
- Cousot & Cousot, POPL 1979 — <https://doi.org/10.1145/567752.567778>
- Rocq Bottom, SAS 2026 — <https://conf.researchr.org/details/splash-issta-2026/sas-2026-papers/20/Rocq-Bottom-Beyond-Soundness-with-Precise-Reasoning-about-Analysis-Precision>

Known by citation but not re-opened in this pass; verify before submission:
TGC 2010 (Besson–Jensen–Pichardie–Turpin), Wildmoser–Chaieb–Nipkow ENTCS 2005,
ICFP 2024 (Michelland–Zakowski–Gonnord), CPP 2026 (Trabish–Itzhaky), Boulmé et
al. JAR 2019, Rival–Mauborgne TOPLAS 2007, Goblint Validator TACAS 2024,
LeanVIPR NeurIPS 2026, LeanMVerify (Zenodo 20726909).
