import CertCore.Cert
import CertCore.Domain

/-!
# `CertCore.Check` — trusted

The checker: three obligation families, a typed diagnostic, and **no search**
(project plan §4.1, §5).

Status: **M3.3.** The diagnostic, certificate lookup, structural certificate
validation and the `check` skeleton are in; the init/edge/safety obligations are
M3.4–M3.6.

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

/-- The certificate lookup at a point and label, with the v1 defaults:
`some a` for a present state, `none` for an explicit `bot`, and `D.top` for a
missing key. -/
def Certificate.stateAt (D : CertDomain) (c : Certificate D.Abs)
    (p : Point) (l : Label) : Option D.Abs :=
  match c.lookup? p l with
  | some none => none
  | some (some a) => some a
  | none => some D.top

/-- The entry state, or `none` for the v1 `bot` marker. -/
def Certificate.entryAt {Abs : Type} (c : Certificate Abs) : Option Abs :=
  c.entry.state

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

/-! ## M3.3 skeleton

The signature and total failure behaviour are fixed here. `check` validates the
structural shape of the typed certificate and returns `.ok ()`; M3.4–M3.6 insert
the three obligation families. A malformed shape is a typed `Diagnostic`, never
a crash. -/

/-- The checker. The skeleton currently validates the certificate shape and
returns success; semantic obligations are added by M3.4–M3.6. -/
def check (_D : CertDomain) (p : Program) (cert : Certificate _D.Abs) :
    CheckResult _D.Abs Unit :=
  if cert.wellFormed p then
    .ok ()
  else
    .error (Diagnostic.malformed "malformed certificate shape")

end CertCore
