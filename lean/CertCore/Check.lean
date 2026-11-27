import CertCore.Cert

/-!
# `CertCore.Check` — trusted

The checker: three obligation families, a typed diagnostic, and **no search**
(project plan §4.1, §5).

Status: **M3.2.** The diagnostic type and the `Except` result plumbing are in;
the checker skeleton and obligations follow at M3.3–M3.6.

Obligations (each decided by a `ble` or `entails` call):

* **init** — `ble (initOf p) (at entry)`
* **edge** — for every CFG edge `(p, c, q)`: `ble (transfer c (at p)) (at q)`
* **safety** — at every assert and every partial operation:
  `entails (at p) (safePred p)`

A rejection is a **value**, not a string: `Diagnostic Abs` names the obligation,
the point/label, the edge (when there is one), and the expected/actual abstract
states. M4's total decoder uses the same type for `malformed`,
`unsupportedDomain`, and `hashMismatch`.
-/

namespace CertCore

/-- The reason a certificate was rejected. These are the v1 diagnostic kinds
(`certificate-v1.md` §8) plus the three obligation families. -/
inductive Obligation where
  /-- The certificate bytes were malformed (decoder, M4). -/
  | malformed
  /-- The domain tag is not supported (decoder, M4). -/
  | unsupportedDomain
  /-- The program hash did not match (decoder/checker, M4). -/
  | hashMismatch
  /-- The entry state does not contain the program's initial state. -/
  | init
  /-- An edge's transferred state is not included in the claimed successor. -/
  | edge
  /-- A safety predicate is not entailed at a risky point. -/
  | safety
  deriving DecidableEq, Repr

/-- A typed rejection.

`expected`/`actual` are optional because not every diagnostic has abstract
states (`malformed`, `hashMismatch`); `edge` is set for edge failures and
`label` for every labelled obligation. `detail` carries decoder/hash text
without turning the verdict into an untyped string. -/
structure Diagnostic (Abs : Type) where
  /-- The obligation family or decoder failure. -/
  kind : Obligation
  /-- Program point, when the failure is point-indexed. -/
  point : Option Point
  /-- Label index, when the failure is label-indexed. -/
  label : Option Label
  /-- The failed edge, for `edge` diagnostics. -/
  edge : Option Edge
  /-- What the checker required (or expected). -/
  expected : Option Abs
  /-- What the certificate claimed (or supplied). -/
  actual : Option Abs
  /-- Decoder/hash detail; empty for ordinary obligation failures. -/
  detail : String
  deriving Repr

namespace Diagnostic

/-- A decoder failure. -/
def malformed {Abs : Type} (detail : String) : Diagnostic Abs :=
  { kind := .malformed, point := none, label := none, edge := none,
    expected := none, actual := none, detail := detail }

/-- An unsupported domain tag. -/
def unsupportedDomain {Abs : Type} (detail : String) : Diagnostic Abs :=
  { kind := .unsupportedDomain, point := none, label := none, edge := none,
    expected := none, actual := none, detail := detail }

/-- A program-hash mismatch. -/
def hashMismatch {Abs : Type} (detail : String) : Diagnostic Abs :=
  { kind := .hashMismatch, point := none, label := none, edge := none,
    expected := none, actual := none, detail := detail }

/-- The entry state failed to contain the initial state. -/
def init {Abs : Type} (point : Point) (label : Label)
    (expected actual : Abs) : Diagnostic Abs :=
  { kind := .init, point := some point, label := some label, edge := none,
    expected := some expected, actual := some actual, detail := "" }

/-- An edge inclusion failed. -/
def ofEdge {Abs : Type} (e : Edge) (label : Label)
    (expected actual : Abs) : Diagnostic Abs :=
  { kind := .edge, point := some e.src, label := some label, edge := some e,
    expected := some expected, actual := some actual, detail := "" }

/-- A safety entailment failed. -/
def safety {Abs : Type} (point : Point) (label : Label) (expected : Abs)
    (detail : String := "") : Diagnostic Abs :=
  { kind := .safety, point := some point, label := some label, edge := none,
    expected := some expected, actual := none, detail := detail }

end Diagnostic

/-- The checker/decoder result type: success is the requested value; failure is
a typed `Diagnostic`, never a string. -/
abbrev CheckResult (Abs : Type) (α : Type) := Except (Diagnostic Abs) α

end CertCore
