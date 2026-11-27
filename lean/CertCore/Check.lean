import CertCore.Cert
import CertCore.Domain

/-!
# `CertCore.Check` — trusted

The checker: three obligation families, a typed diagnostic, and **no search**
(project plan §4.1, §5).

Status: **M3.5.** The diagnostic, lookup, shape validation, init and edge
obligations are in; the safety obligation and T5 are M3.6–M3.7.

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

/-- An edge whose successor state is explicitly `bot`. -/
def ofEdgeBot {Abs : Type} (e : Edge) (label : Label) (expected : Abs) :
    Diagnostic Abs :=
  { kind := .edge, point := some e.src, label := some label, edge := some e,
    expected := some expected, actual := none, detail := "target state is bot" }

/-- A safety entailment failed. -/
def safety {Abs : Type} (point : Point) (label : Label) (expected : Abs)
    (detail : String := "") : Diagnostic Abs :=
  { kind := .safety, point := some point, label := some label, edge := none,
    expected := some expected, actual := none, detail := detail }

end Diagnostic

/-- The checker/decoder result type: success is the requested value; failure is
a typed `Diagnostic`, never a string. -/
abbrev CheckResult (Abs : Type) (α : Type) := Except (Diagnostic Abs) α

/-! ## M3.4 init obligation

The checker's base case is `ble (initOf p) (at entry)` for every label at the
entry point. The certificate's `entry` supplies its own label; other labels at
the same point use the sparse map, and a missing label is `⊤`. -/

/-- The state used by the init obligation: the certificate's `entry` for its own
`(point,label)`, and the sparse map for every other label at the entry point. -/
def Certificate.stateAtEntry (D : CertDomain) (c : Certificate D.Abs)
    (p : Point) (l : Label) : Option D.Abs :=
  if p = c.entry.point ∧ l = c.entry.label then
    c.entry.state
  else
    c.stateAt D p l

/-- The init diagnostic when the entry state is explicitly `bot`. -/
def Diagnostic.initBot {Abs : Type} (point : Point) (label : Label)
    (expected : Abs) : Diagnostic Abs :=
  { kind := .init, point := some point, label := some label, edge := none,
    expected := some expected, actual := none, detail := "entry state is bot" }

/-- Check `ble (initOf p) (at entry)` for every label at the entry point.
Missing labels are `⊤`; an explicit `bot` entry cannot contain the initial
state, so it is rejected. -/
def checkInitFrom (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    List Label → CheckResult D.Abs Unit
  | [] => .ok ()
  | l :: ls =>
      match cert.stateAtEntry D cert.entry.point l with
      | none =>
          .error (Diagnostic.initBot cert.entry.point l (D.initOf p))
      | some a =>
          if D.ble (D.initOf p) a then
            checkInitFrom D p cert ls
          else
            .error (Diagnostic.init cert.entry.point l (D.initOf p) a)

/-- The init obligation for all labels of the certificate. -/
def checkInit (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    CheckResult D.Abs Unit :=
  checkInitFrom D p cert (List.range cert.labels)

/-! ## M3.5 edge obligation

For every CFG edge and every label, check
`ble (transfer c (at src)) (at dst)`. This M3.5 instance uses the identity label
update (the flat `none` scheme); branch-history successor labels are M9.3. A
missing target state is `⊤`; an explicit `bot` target is a failure unless the
source is itself unreachable (`bot`), in which case the edge is skipped.

Labels are checked by `List.range cert.labels`; the shape contract guarantees
`1 ≤ labels ≤ 64`. -/

/-- Edge obligations for one edge, over every label. -/
def checkEdgeLabels (D : CertDomain) (p : Program) (cert : Certificate D.Abs)
    (e : Edge) : List Label → CheckResult D.Abs Unit
  | [] => .ok ()
  | l :: ls =>
      match cert.stateAtEntry D e.src l with
      | none =>
          -- The source point is explicitly unreachable for this label.
          checkEdgeLabels D p cert e ls
      | some src =>
          let expected := D.transfer e.cmd src
          match cert.stateAtEntry D e.dst l with
          | none => .error (Diagnostic.ofEdgeBot e l expected)
          | some actual =>
              if D.ble expected actual then
                checkEdgeLabels D p cert e ls
              else
                .error (Diagnostic.ofEdge e l expected actual)

/-- Edge obligations over a list of edges. -/
def checkEdgesFrom (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    List Edge → CheckResult D.Abs Unit
  | [] => .ok ()
  | e :: es =>
      match checkEdgeLabels D p cert e (List.range cert.labels) with
      | .ok () => checkEdgesFrom D p cert es
      | .error d => .error d

/-- Edge obligations over the compiled CFG. -/
def checkEdges (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    CheckResult D.Abs Unit :=
  checkEdgesFrom D p cert (Program.compile p).edges

/-- The checker: shape, init, then edge obligations. Safety is M3.6. -/
def check (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    CheckResult D.Abs Unit :=
  if cert.wellFormed p then
    match checkInit D p cert with
    | .error d => .error d
    | .ok () => checkEdges D p cert
  else
    .error (Diagnostic.malformed "malformed certificate shape")

end CertCore
