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

The map is stored as a **row-major array** indexed by
`point * labels + label`, not as a list. Lookup is therefore O(1), the array
cannot contain duplicate keys, and `wellFormed` is linear in the number of
labels (plus one compilation of the program). The array length is
`points * labels`; `none` is a missing key (`⊤`) and `some none` is the v1
`{"kind":"bot"}` marker.

The domain tag, format version and program hash are decoder metadata (M4), not
checker data, so they are not part of this type yet.

Status: **M3.1 type; M3.3 checker integration.** JSON decoding is M4.
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

/-- The Lean-side certificate: the entry entry plus a row-major state array.

`points` is the size of the compiled CFG's instruction array (`entry` included),
so `|Points|` in v1 §3.1; `labels` is `labels.size`. The array has exactly
`points * labels` cells. Sortedness is irrelevant to an array; uniqueness is
structural. The checker validates the length, the entry cell and the halt row.
-/
structure Certificate (Abs : Type) where
  /-- Number of labels (`labels.size`). -/
  labels : Nat
  /-- Number of points (`((Program.compile p).instrs.size)`). -/
  points : Nat
  /-- Entry point, label and state. -/
  entry : StateAt Abs
  /-- Row-major `point * labels + label ↦ Option (Option Abs)`. -/
  states : Array (Option (Option Abs))
  deriving Repr

namespace Certificate

/-- Build a certificate from sparse `(point,label)` entries. Intended for tests
and the M4 decoder; out-of-range entries are ignored (the decoder must reject
them before this constructor). -/
def ofSparse {Abs : Type} (labels points : Nat) (entry : StateAt Abs)
    (cells : List (StateAt Abs)) : Certificate Abs :=
  { labels := labels,
    points := points,
    entry := entry,
    states :=
      cells.foldl
        (fun a s => a.set! (s.point * labels + s.label) (some s.state))
        (Array.replicate (points * labels) none) }

/-- The abstract state at the entry, or `none` for the v1 `bot` marker. -/
def entryState {Abs : Type} (c : Certificate Abs) : Option Abs :=
  c.entry.state

/-- The entry point. -/
def entryPoint {Abs : Type} (c : Certificate Abs) : Point :=
  c.entry.point

/-- The entry label. -/
def entryLabel {Abs : Type} (c : Certificate Abs) : Label :=
  c.entry.label

/-- O(1) cell access. `none` is an absent key; `some s` is a present state or
the explicit `bot` marker (`some none`). Out-of-range coordinates answer `none`,
exactly like a missing key; the shape contract prevents them from passing
`check`. -/
def cellAt {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) :
    Option (Option Abs) :=
  if p < c.points ∧ l < c.labels then
    match c.states[p * c.labels + l]? with
    | some cell => cell
    | none => none
  else
    none

/-- Is the cell absent? A pattern match, not an equality on `Abs`, so this needs
no `DecidableEq` instance (and cannot pull in `Classical.choice`). -/
def cellAbsent {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) : Bool :=
  match cellAt c p l with
  | none => true
  | some _ => false

/-- O(1) lookup. -/
def lookup? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) :
    Option (Option Abs) :=
  cellAt c p l

/-- The raw entry at `(p, l)`, if present. Unlike `lookup?`, this distinguishes a
missing key (`none`) from a present `bot` entry (`some ⟨…, none⟩`). -/
def find? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) :
    Option (StateAt Abs) :=
  match lookup? c p l with
  | some st => some { point := p, label := l, state := st }
  | none => none

/-- Is the point's state explicitly `bot`? Missing keys answer `false` (they are
`⊤`, not `bot`). -/
def isBot? {Abs : Type} (c : Certificate Abs) (p : Point) (l : Label) : Bool :=
  match lookup? c p l with
  | some none => true
  | _ => false

/-- The array cell for the halt point and a label is absent. v1 §3.1: the halt
point carries no certificate state. -/
def haltRowEmpty {Abs : Type} (c : Certificate Abs) : Bool :=
  (List.range c.labels).all (fun l => cellAbsent c (c.points - 1) l)

/-- Structural well-formedness of a certificate for a program (M3.3/M4).

This is the shape contract, not the semantic invariant: labels are in v1 range,
the point count is the compiled CFG's array size, the entry point is the
program's entry point, the array has exactly `points * labels` cells, the entry
key is absent from `states`, and the halt row is empty. There are no duplicate
keys because the array is indexed by `(point,label)`.

The decoder will enforce the same rules on the wire; the checker validates the
typed value again so that a directly constructed `Certificate` cannot bypass
them. Semantic obligations (init, edges, safety) are M3.4–M3.6, not here. -/
def wellFormed {Abs : Type} (p : Program) (c : Certificate Abs) : Bool :=
  Nat.blt 0 c.labels &&
  Nat.ble c.labels 64 &&
  (c.points == (Program.compile p).instrs.size) &&
  Nat.blt c.entry.label c.labels &&
  (c.entry.point == p.entry) &&
  (c.states.size == c.points * c.labels) &&
  cellAbsent c c.entry.point c.entry.label &&
  c.haltRowEmpty

/-- Propositional form of `wellFormed`, for checker soundness proofs. -/
def WellFormed {Abs : Type} (p : Program) (c : Certificate Abs) : Prop :=
  c.wellFormed p = true

end Certificate

end CertCore
