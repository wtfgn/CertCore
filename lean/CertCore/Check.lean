import CertCore.Cert
import CertCore.Domain

/-!
# `CertCore.Check` — trusted

The checker: three obligation families, a typed diagnostic, and **no search**
(project plan §4.1, §5).

Status: **M3.6.** The diagnostic, lookup, shape validation, init, edge and
safety obligations are in; T5 is M3.7.

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

/-- The state used by the init obligation: the certificate's `entry` for its own
`(point,label)`, and the sparse map for every other label at the entry point. -/
def Certificate.stateAtEntry (D : CertDomain) (c : Certificate D.Abs)
    (p : Point) (l : Label) : Option D.Abs :=
  if p = c.entry.point ∧ l = c.entry.label then
    c.entry.state
  else
    c.stateAt D p l

/-! ## M3.6 safety predicates

Safety obligations are structural, derived from the compiled instruction at a
point. `assert b` requires `b` (truth and definedness); a branch requires only
that the guard is **defined** (either outcome is allowed). Expressions get a
syntactic definedness predicate:

* `+`/`-`/`*`: both operands defined and the operation itself does not fail
  (the equality `e = e` is true exactly when `eval e` succeeds);
* `/`: operands defined, divisor non-zero, and not `min / -1`;
* `read a i`: index expression defined and `0 ≤ i < len a`;
* `len a`: the length is representable.

`entails` decides these predicates. It is conservative for multiplication and
division inside conditions (it returns `false`), so such programs are rejected,
not accepted unsoundly. -/

/-- A structural always-true predicate. -/
def safeTrue : BExp := .cmp .eq (.const I32.zero) (.const I32.zero)

/-- Conjunction of safety predicates. -/
def safeAnd (a b : BExp) : BExp := .and a b

/-- Definedness of an expression, as a predicate over the pre-state. -/
def exprSafe : Expr → BExp
  | .const _ => safeTrue
  | .var _ => safeTrue
  | .add l r =>
      safeAnd (exprSafe l)
        (safeAnd (exprSafe r) (.cmp .eq (.add l r) (.add l r)))
  | .sub l r =>
      safeAnd (exprSafe l)
        (safeAnd (exprSafe r) (.cmp .eq (.sub l r) (.sub l r)))
  | .mul l r =>
      safeAnd (exprSafe l)
        (safeAnd (exprSafe r) (.cmp .eq (.mul l r) (.mul l r)))
  | .div l r =>
      safeAnd (exprSafe l)
        (safeAnd (exprSafe r)
          (safeAnd (.cmp .ne r (.const I32.zero))
            (.not (safeAnd (.cmp .eq l (.const I32.min))
              (.cmp .eq r (.const (I32.ofIntWrap (-1))))))))
  | .read a i =>
      safeAnd (exprSafe i)
        (safeAnd (.cmp .le (.const I32.zero) i) (.cmp .lt i (.len a)))
  | .len a => .cmp .eq (.len a) (.len a)

/-- Definedness of a condition. A branch is safe when its guard is defined; the
comparison's truth is not required because either outcome is a valid step. -/
def bexpDefined : BExp → BExp
  | .cmp _ l r => safeAnd (exprSafe l) (exprSafe r)
  | .not b => bexpDefined b
  | .and l r => safeAnd (bexpDefined l) (bexpDefined r)
  | .or l r => safeAnd (bexpDefined l) (bexpDefined r)

/-- Safety predicate of an atomic instruction. -/
def atomicSafe : AtomicCmd → BExp
  | .skip => safeTrue
  | .assign _ e => exprSafe e
  | .store a i v =>
      safeAnd (exprSafe i)
        (safeAnd (exprSafe v)
          (safeAnd (.cmp .le (.const I32.zero) i) (.cmp .lt i (.len a))))
  | .assert b => b

/-- Safety predicate of a compiled instruction. -/
def instrSafe : Instr → BExp
  | .atomic cmd _ => atomicSafe cmd
  | .branch b _ _ => bexpDefined b

/-- Safety obligations for one point and every label. `bot` skips the point. -/
def checkSafetyLabels (D : CertDomain) (cert : Certificate D.Abs)
    (instr : Instr) (point : Point) : List Label → CheckResult D.Abs Unit
  | [] => .ok ()
  | l :: ls =>
      match cert.stateAtEntry D point l with
      | none => checkSafetyLabels D cert instr point ls
      | some a =>
          if D.entails a (instrSafe instr) then
            checkSafetyLabels D cert instr point ls
          else
            .error (Diagnostic.safety point l a "safety predicate not entailed")

/-- Safety obligations over a list of points of an already compiled CFG. -/
def checkSafetyPoints (D : CertDomain) (cert : Certificate D.Abs) (cfg : CFG) :
    List Point → CheckResult D.Abs Unit
  | [] => .ok ()
  | pt :: pts =>
      match cfg.instrAt pt with
      | none => checkSafetyPoints D cert cfg pts
      | some instr =>
          match checkSafetyLabels D cert instr pt (List.range cert.labels) with
          | .ok () => checkSafetyPoints D cert cfg pts
          | .error d => .error d

/-- Safety obligations over every point of the compiled CFG. The CFG is compiled
once, not per point, so the checker stays linear in the certificate/program
size. -/
def checkSafety (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    CheckResult D.Abs Unit :=
  let cfg := Program.compile p
  checkSafetyPoints D cert cfg (List.range cfg.instrs.size)

/-! ## M3.4 init obligation

The checker's base case is `ble (initOf p) (at entry)` for every label at the
entry point. The certificate's `entry` supplies its own label; other labels at
the same point use the sparse map, and a missing label is `⊤`. -/

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

/-- The checker: shape, init, edge, then safety obligations. -/
def check (D : CertDomain) (p : Program) (cert : Certificate D.Abs) :
    CheckResult D.Abs Unit :=
  if cert.wellFormed p then
    match checkInit D p cert with
    | .error d => .error d
    | .ok () =>
        match checkEdges D p cert with
        | .error d => .error d
        | .ok () => checkSafety D p cert
  else
    .error (Diagnostic.malformed "malformed certificate shape")

end CertCore
