import CertCore.Semantics

/-!
# `CertCore.Cert` — trusted

The Lean-side **certificate type** (M3.1). JSON encoding and the total decoder
are M4; this module is only the data the checker consumes.

The shape follows the frozen v1 format (`docs/certificate-v1.md`): an `entry`
state and a sparse `(point, label) ↦ state` map. Two fields from the plan's
original sketch are deliberately absent: per-edge successor labels and
per-assertion states. They were dropped in v1 (§10) because the checker
recomputes labels from the semantics and derives safety points from the AST; a
certificate supplies states only.

A point's state is `Option Abs`: `none` is the v1 `{"kind":"bot"}` coverage
marker, while a missing `(point, label)` entry is `⊤` and is represented by the
lookup returning `none` at the outer level. The domain tag, format version and
program hash are decoder metadata (M4), not checker data, so they are not part of
this type yet.

Status: **M3.1.** No `check`/`decode` yet; the diagnostic is M3.2.
-/

namespace CertCore

/-- Flat label index for v1 (`labels.kind = "flat"`). -/
abbrev Label := Nat

/-- One entry of the sparse certificate map: a point, a label, and either an
abstract state or the explicit `bot` marker (`none`). -/
structure StateAt (Abs : Type) where
  /-- Program point (an index into the compiled CFG's instruction array). -/
  point : Point
  /-- Flat label index. -/
  label : Label
  /-- `some a` is an abstract state; `none` is the v1 `bot` marker. -/
  state : Option Abs
  deriving Repr

/-- The Lean-side certificate: the entry entry plus a sparse state list.

`labels` is the partition size (`labels.size` in v1); the checker needs it to
enumerate the label space. Sortedness, uniqueness, and in-range checks are the
decoder's/checker's job (M3.3/M4), not invariants of this type. -/
structure Certificate (Abs : Type) where
  /-- Number of labels (`labels.size`). -/
  labels : Nat
  /-- Entry point, label and state. -/
  entry : StateAt Abs
  /-- Sparse `(point, label) ↦ state` map. Missing keys mean `⊤`. -/
  states : List (StateAt Abs)
  deriving Repr

namespace Certificate

/-- The abstract state at the entry, or `none` for the v1 `bot` marker. -/
def entryState {Abs : Type} (c : Certificate Abs) : Option Abs :=
  c.entry.state

/-- The entry point. -/
def entryPoint {Abs : Type} (c : Certificate Abs) : Point :=
  c.entry.point

/-- The entry label. -/
def entryLabel {Abs : Type} (c : Certificate Abs) : Label :=
  c.entry.label

/-- Does a certificate entry carry the key `(p, l)`? -/
def keyMatches {Abs : Type} (s : StateAt Abs) (p : Point) (l : Label) : Bool :=
  s.point == p && s.label == l

/-- The raw entry at `(p, l)`, if present. Unlike `lookup?`, this distinguishes a
missing key (`none`) from a present `bot` entry (`some ⟨…, none⟩`). -/
def find? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) :
    Option (StateAt Abs) :=
  c.states.find? (fun s => keyMatches s p l)

/-- Look up the state at `(p, l)`:
* `some (some a)` — the certificate claims abstract state `a`;
* `some none` — the certificate explicitly marks the point as `bot`;
* `none` — the key is absent, i.e. the v1 default `⊤`. -/
def lookup? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) :
    Option (Option Abs) :=
  (find? c p l).map (fun s => s.state)

/-- Is the point's state explicitly `bot`? Missing keys answer `false` (they are
`⊤`, not `bot`). -/
def isBot? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) : Bool :=
  match lookup? c p l with
  | some none => true
  | _ => false

/-- The `(point, label)` key of one certificate entry. -/
def key {Abs : Type} (s : StateAt Abs) : Point × Label :=
  (s.point, s.label)

/-- All keys of the sparse map, in certificate order. -/
def keys {Abs : Type} (c : Certificate Abs) : List (Point × Label) :=
  c.states.map key

/-- Structural well-formedness of a certificate for a program (M3.3/M4).

This is the shape contract, not the semantic invariant: labels are in v1 range,
the entry point is the program's entry point, every state key is in range, keys
are unique, and the entry key is not repeated in `states`. The decoder will
enforce the same rules on the wire; the checker validates the typed value again
so that a directly constructed `Certificate` cannot bypass them.

Semantic obligations (init, edges, safety) are M3.4–M3.6, not here. -/
def wellFormed {Abs : Type} (p : Program) (c : Certificate Abs) : Bool :=
  Nat.blt 0 c.labels &&
  Nat.ble c.labels 64 &&
  Nat.blt c.entry.label c.labels &&
  (c.entry.point == p.entry) &&
  c.states.all (fun s =>
    Nat.blt s.label c.labels &&
    Nat.blt s.point (Program.compile p).instrs.size) &&
  (c.keys.eraseDups.length == c.keys.length) &&
  !(c.keys.elem (c.entry.point, c.entry.label))

/-- Propositional form of `wellFormed`, for checker soundness proofs. -/
def WellFormed {Abs : Type} (p : Program) (c : Certificate Abs) : Prop :=
  c.wellFormed p = true

end Certificate

end CertCore
