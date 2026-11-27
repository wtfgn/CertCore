# Certificate format v1

| | |
|---|---|
| Status | **Frozen for M0.5** — this is the interface between the untrusted analyzer and the trusted checker |
| Format string | `certcore/1` |
| Companion | Project plan §10.3 (sketch), §4.2 (what is checked), roadmap M0.5 |
| Change rule | Changing this after M4.2 costs roughly a day. Read §11 before editing |

The certificate is the only interface between the analyzer and the verdict.
Everything in this document is therefore part of the protocol, not an
implementation detail: two independent implementations (Lean checker, Haskell
emitter) must agree byte-for-byte on what a certificate *means*.

## 1. Design constraints

1. **The checker performs no search.** The certificate supplies abstract states;
   every obligation is one decidable inclusion test. Nothing in the format may
   require the checker to explore, enumerate, or fixpoint.
2. **Every byte is load-bearing.** Certificate size is the measured quantity in
   claim C4, so redundant fields are not free — they distort the frontier. This
   is why two fields from the plan's sketch are dropped (§10).
3. **The decoder is total.** Malformed input is a `Diagnostic.malformed`, never
   a crash, and cannot induce super-linear work (T10, requirement R4).
4. **Human-readable.** JSON, not a binary blob: a rejected certificate must be
   readable by a human, because debuggability is a design goal (R6, plan D4).
5. **Hash-pinned.** A certificate names the program it certifies, so it cannot
   be silently transplanted.

## 2. Encoding rules

- UTF-8 JSON. Numbers are **integers only** — no floats, no exponents, no
  leading `+`, no leading zeros beyond `0` itself.
- `null` is allowed only where this document says so (interval bounds).
- **Unknown object fields are rejected at every level.** v1 has no optional
  fields, so a misspelt key is a malformed certificate, not a silently ignored
  hint.
- **Canonical form.** `states` is sorted ascending by `(point, label)`. An
  encoder MUST emit that order (it makes byte counts comparable across runs and
  diffs readable). A decoder accepts any order but rejects duplicate keys.
- **Within a state**, `vars` keys are sorted ascending by variable name, for the
  same reason and with the same decoder rule.
- Strings are UTF-8; the only strings in v1 are frozen literals (`details`) and
  program variable names.

## 3. Top level

All six fields are required.

```json
{
  "format": "certcore/1",
  "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
  "domain": { "kind": "interval" },
  "labels": { "kind": "flat", "size": 1, "scheme": "none" },
  "entry": { "point": 0, "label": 0, "state": { "kind": "itv", "vars": {} } },
  "states": [
    { "point": 1, "label": 0, "state": { "kind": "itv", "vars": { "x": { "lo": 0, "hi": 0 } } } }
  ]
}
```

| Field | Type | Meaning |
|---|---|---|
| `format` | string, exactly `"certcore/1"` | Version. Anything else ⇒ malformed |
| `program_hash` | 64 lowercase hex chars | SHA-256 of the canonical AST JSON (§4) |
| `domain` | object | Numerical abstract domain (§5) |
| `labels` | object | Partition descriptor (§6) |
| `entry` | object | Abstract state at the initial point and label |
| `states` | array | Sparse map `(point, label) ↦ Abs` (§3.1) |

### 3.1 `entry` and `states`

```text
{ "point": 0, "label": 0, "state": { … } }
```

- `point` is a non-negative integer in `[0, |Points|)`, where `|Points|` is the
  size of the compiled CFG's instruction array: every source program point plus
  one halt point. For dense source points `0 .. maxPoint`, that is
  `maxPoint + 2`. Out of range ⇒ malformed. The halt point is not a source point
  and carries no certificate state; the frontend guarantees dense unique source
  points (`Program.WF`), and the checker uses the same array size as the bound.
- `label` is a non-negative integer in `[0, labels.size)`. Out of range ⇒
  malformed.
- `states` must not contain the `entry` key, and must not contain duplicate
  `(point, label)` keys. Both ⇒ malformed.
- The map is **partial**: a missing `(point, label)` denotes `⊤` (§7).

## 4. `program_hash`

`program_hash` is the lowercase hex SHA-256 of the exact UTF-8 bytes of the
canonical AST JSON document that the trusted frontend emits and hands to the
analyzer. Canonical means: object keys sorted lexicographically at every level,
no insignificant whitespace, integers only, `states`-style arrays omitted from
the AST entirely (the AST has no certificate content).

The checker recomputes the hash from the AST it parsed and compares. A mismatch
is `Diagnostic.hashMismatch` — a *diagnostic*, not a soundness mechanism: even
after a collision the checker still validates every obligation against the real
program. The hash exists so that "wrong certificate for this program" is a
localised error instead of a baffling edge failure.

## 5. Abstract domains and state encoding

v1 ships exactly one numerical domain. The `kind` tag makes further domains
additive (§11).

### 5.1 Interval (`"domain": {"kind": "interval"}`)

State is one of:

| Encoding | Meaning |
|---|---|
| `{"kind":"itv","vars":{…},"mem":{…}}` | a partial map from variable names to intervals, plus an optional map from array numbers to one interval covering every cell; an absent variable or array is unconstrained (`⊤`) |
| `{"kind":"bot"}` | the empty set: the point (and label) is unreachable |

- Each interval is `{"lo": L, "hi": H}`, where `L`, `H` are integers in
  `[-2147483648, 2147483647]` or `null`. `lo: null` means −∞, `hi: null`
  means +∞.
- Both bounds present ⇒ must satisfy `L ≤ H`; otherwise malformed. (An
  ill-formed interval is the classic soundness trap: `ble` on `[5, 3]` would
  answer "contained in everything". The decoder refuses it.)
- An empty interval is not an encoding of bottom: `L > H` is malformed, and
  unreachability is `bot`.
- **`⊤` is encoded by omission.** An absent variable is unconstrained, so an
  explicit unbounded interval (`{"lo":null,"hi":null}`) is malformed. The same
  rule applies to `mem`: an absent array has the unconstrained summary `⊤`.
  Each abstract state therefore has exactly one encoding, and a state with every
  variable and array unconstrained is `{"kind":"itv","vars":{}}`.
- Variable names must be variables of the checked program; an unknown name ⇒
  malformed. `bot` carries no `vars` and no `mem`.
- `mem` is optional. Its keys are decimal array numbers (the declaration order
  from `docs/imp-syntax.md`); an unknown array number ⇒ malformed. The interval
  is a summary: every in-bounds cell of that array must lie in it. The array's
  length is the program's declared length, not a certificate field. This is what
  makes the M2.7 read/len transfer reachable end-to-end: absent array = `⊤`,
  present array = the analyzer's summary.

An example with an array summary (array 0's cells all in `[10,20]`):

```json
{"kind":"itv","vars":{"x":{"lo":0,"hi":0}},"mem":{"0":{"lo":10,"hi":20}}}
```

**Compatibility.** `mem` is a backward-compatible *extension* of the frozen
`certcore/1` state schema: a certificate that omits it means “every array is
`⊤`”, and that is exactly the pre-`mem` encoding. A certificate that uses `mem`
requires a decoder that knows the field; a strict old decoder would reject it as
an unknown field. Since no decoder exists yet, M4.1 must either (a) keep
`certcore/1` and add the optional field with a decoder test, or (b) bump the
format version for certificates that use `mem`. Record the choice with M4.2;
until then, emit `mem` only for a `certcore/1`+`mem`-aware consumer.

### 5.2 Reserved kinds (not in v1)

`"domain": {"kind":"product","left":…,"right":…}` with state
`{"kind":"prod","left":…,"right":…}` is reserved for M6; `{"kind":"octagon"}`
for the post-month M7. Adding a *new* variant is backward compatible (§11); a
v1 decoder rejects them as `unsupportedDomain`, which is a malformed verdict,
not a crash.

## 6. Labels and the partition

```json
{ "labels": { "kind": "flat", "size": 4, "scheme": "branch-history" } }
```

- `kind` is `"flat"`: the label domain is `{0, …, size−1}` (flat, no order).
- `size` ∈ `[1, 64]`.
- `scheme` is `"none"` (iff `size = 1`) or `"branch-history"` (iff
  `size = 2^k`, `k ∈ [1, 6]`). There is exactly one encoding of each partition:
  `none` is depth 0.
- `none` means no partitioning: every state has `label: 0`.
- `branch-history` means the label records the last `k` outcomes of branches
  actually taken: the most recent outcome is the least significant bit, and
  `κ' = ((κ << 1) | b) mod 2^k` when an `if`/`while` takes outcome `b ∈ {0,1}`;
  for every other command `κ' = κ`; initially `κ = 0`.

Because the update is a total function of `(κ, edge)` defined by the trusted
semantics, **the certificate does not carry successor labels**: the checker
recomputes them. That is a deliberate deletion (§10), and it is what keeps
partitioning from adding either bytes or search.

## 7. Coverage: a partial map, and the `⊤` default

`states` is sparse. The invariant the checker verifies is

```text
I(point, κ) = states(point, κ)   if present
            = ⊤                  otherwise
```

Why `⊤` rather than "reject missing states": rejecting would need a reachability
computation in the checker — a search, forbidden by R4. With `⊤` the induction
is still sound (⊤ contains every reachable state), and every edge *into* a
missing state is discharged trivially; but any safety obligation at that point
must then hold for **all** states, so omitting states forfeits precision, never
soundness. An analyzer that omits a reachable state will normally see its safety
obligation fail, not pass.

The explicit `{"kind":"bot"}` state is a coverage marker: the checker represents a
point's state as `Option Abs` (`none` = bot) and skips that point's obligations.
It is not a `CertDomain` element (see the note at the end of `Domain.lean`):
with a support-restricted `gamma`, an all-`bot` abstract state is not
distinguishable from a non-empty one when the support is empty.

## 8. What the checker verifies

The obligations are derived from the program, never from the certificate. The
certificate supplies states only.

| Obligation | Statement | Cost |
|---|---|---|
| **init** | `γ(entry.state) ⊇ Init` | 1 `ble` per label at the entry point |
| **edge** | for every CFG edge `(p, c, q)`, every `κ`, and every semantic successor label `κ'` of `(c, κ)`: `ble (transfer c (I(p,κ))) (I(q,κ'))` | 1 `ble` per (edge × label × successor) |
| **safety** | for every point `p` with a partial operation or `assert`, and every `κ`: the domain's **entailment test** accepts `I(p,κ)` for the predicate at `p` — e.g. an interval `[1,5]` entails `x ≠ 0`, and an index interval inside `[0, len)` entails `0 ≤ i < len`. The test is a domain operation, not a certificate field, because the predicate is structural | 1 entailment test per (obligation × label) |
| **hash** | `program_hash` equals the SHA-256 of the parsed AST's canonical JSON | 1 hash |

A rejected certificate yields a diagnostic naming the obligation kind, the point,
the label, the command (for edges), and the expected/actual abstract states —
a value, not a message (R6). v1 diagnostic kinds: `malformed`,
`unsupportedDomain`, `hashMismatch`, `init`, `edge`, `safety`.

## 9. Cost model

Let `P` = points, `E` = CFG edges, `K` = `labels.size`, `S` = certificate bytes.

| Phase | Cost |
|---|---|
| decode | `O(S)`, total, no backtracking |
| index into `P × K` | `O(P·K)` |
| obligations | `O((E + P)·K)` calls to `Bool`-valued `ble` and entailment tests |
| memory | `O(P·K)` states |

There is no search anywhere, and `K ≤ 64` bounds the constant. Certificate size
grows as `O((reachable point,label) pairs)`, which is the quantity the
north-star experiment measures (C4).

## 10. Deliberate deviations from the plan's sketch (§10.3)

Two fields from the sketch are **not** in v1:

| Sketch field | Verdict | Why |
|---|---|---|
| `successors` (per-edge successor labels) | dropped | The label update is a total function of `(κ, edge)` in the trusted semantics, so the checker recomputes it. Shipping it would spend bytes on information already implied and inflate the measured cost of partitioning. Predicate-based labels, which *would* need hints, are out of v1 (§12). |
| `assertions` (per-assertion states) | dropped | Safety obligation points are structural (asserts, division, array access), so the checker derives them from the AST. Repeating the state at those points duplicates `states` and distorts certificate-size measurements. The diagnostic already names the point. |

The sketch's remaining fields — version, hash, domain tag, entry, sparse point
map — are kept exactly. If either deletion is rejected on review, restoring them
is cheap now and expensive after M4.2: say so before M3.1.

## 11. Versioning

- `format` is matched **exactly**; unknown versions ⇒ malformed.
- **Additive** changes (a new `domain.kind` or `state.kind`, a new `scheme`)
  do not bump the version: old certificates are unaffected and old decoders
  reject the new variants as `unsupportedDomain`.
- **Breaking** changes (new required field, changed meaning, removed field,
  changed canonicalisation) bump to `certcore/2`.
- The decoder is strict about unknown fields, so any encoder experiment that
  adds a field must also bump.

## 12. Open items — recorded, not silently decided

1. **SHA-256 in Lean.** Lean core ships no cryptography. M4.1 implements it
   (≈100 lines, total, no `partial`), or vendors a vetted total implementation.
   This is the only non-trivial primitive the decoder needs.
2. **Predicate labels.** A label that is a predicate on the pre-state
   (`κ = sign(x)`) does not have a `(κ, edge)`-only update, so the certificate
   would need successor hints plus a new obligation relating abstract states to
   label updates. Out of v1; this is where a future version earns its number.
3. **Coarsened partitions.** v1 requires the analyzer to use the scheme's finest
   partition (`size = 2^k`). Merging labels (trading precision for bytes) needs
   a simulation obligation and successor hints; deferred with §12.2.
4. **Product/octagon encodings.** Reserved in §5.2; finalised at M6/M7 without a
   version bump.
5. **CLI contract** (M4.5): `certcore check prog.imp cert.json` exits `0` on
   accept, `1` on reject with a diagnostic, `2` on malformed input.
6. **Safety entailment is a domain operation (resolved at F1).** The plan's
   `CertDomain` sketch (§4.2) carries only `ble`, and safety cannot be a `ble`
   call: `{x ≠ 0}` is not one interval, so `x ∈ [-5,-1]` is safe but has no
   single interval target to be included in. `CertDomain` now carries
   `entails : Abs → BExp → Bool` and

   ```lean
   entails_sound : entails a b = true → P s → gamma a s → evalB b s = some true
   ```

   The answer is "definitely true" only when every state represented by `a`
   evaluates the predicate to `true` *and* the predicate's expressions are
   defined; `none`/`some false` are both `false` from the checker's point of
   view. The wire format is unaffected (predicates are structural). The interval
   test is conservative — it handles constants, variables, `+`/`-` with finite
   endpoint sums, comparisons, and `not`/`and`/`or`; `*`, `/`, array reads and
   `len` are declined (return `false`). This is a precision limitation, not a
   soundness one; see [`known-gaps.md`](known-gaps.md).
7. **Array memory is in v1 (resolved at F5).** The state carries an optional
   `mem` map (§5.1): absent array = `⊤`, present array = one interval covering
   every in-bounds cell, unknown array number = malformed. The M4.2 decoder must
   enforce the same interval rules as `vars` and reject `bot` states that carry
   `vars`/`mem`. This closes the M2.7-format mismatch: the interval instance's
   `mem` component is now expressible on the wire, so read/len precision is not
   lost at the decoder boundary.

## 13. Worked example

Program (points in comments; `I32` semantics):

```text
0: x := 0          -- entry, x unconstrained before this
1: x := x + 1
2: y := 10 / x     -- safety: x ≠ 0
3: assert (y == 10)
```

A certificate that the interval checker accepts:

```json
{
  "format": "certcore/1",
  "program_hash": "0000000000000000000000000000000000000000000000000000000000000000",
  "domain": { "kind": "interval" },
  "labels": { "kind": "flat", "size": 1, "scheme": "none" },
  "entry": { "point": 0, "label": 0, "state": { "kind": "itv", "vars": {} } },
  "states": [
    { "point": 1, "label": 0, "state": { "kind": "itv", "vars": { "x": { "lo": 0, "hi": 0 } } } },
    { "point": 2, "label": 0, "state": { "kind": "itv", "vars": { "x": { "lo": 1, "hi": 1 } } } },
    { "point": 3, "label": 0, "state": { "kind": "itv", "vars": { "x": { "lo": 1, "hi": 1 }, "y": { "lo": 10, "hi": 10 } } } }
  ]
}
```

Obligations discharged: init (`⊤ ⊇ Init`); edge `0→1` (`x := 0` gives `[0,0]`);
edge `1→2` (`x := x+1` on `[0,0]` gives `[1,1]`); edge `2→3` (`10/x` on `x=1`
gives `y = 10`, and `x` unchanged); safety at 2 (`[1,1]` entails `x ≠ 0`); assert
at 3 (`y = 10`). `y` is omitted at points 0–2 because it is unconstrained there
(§5.1: `⊤` is omission). The `program_hash` here is a placeholder; a real
certificate carries the AST hash.

Flip `states[0].state.vars.x.hi` from `0` to `5` and the edge `1→2` obligation
fails: `x := x + 1` sends `[0,5]` to `[1,6]`, which is not contained in `[1,1]`,
so the diagnostic reads `Diagnostic.edge point=1 expected=[1,1] actual=[1,6]` —
the demo's "catch a lie" moment (plan §12.7).
