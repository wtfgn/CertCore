import CertCore.Check
import CertCore.Domain.IntervalInstance

/-!
# Checker skeleton tests (M3.3)

Run with:

    lake env lean lean/Tests/CheckSkeleton.lean

Pins the row-major lookup (`state` / `bot` / missing-`⊤`), the structural
certificate validation, and the total `check` skeleton. Semantic obligations are
deliberately absent at M3.3.
-/

open CertCore
open CertCore.Interval

def D : CertDomain := intervalDomain (fun _ => 0) ["x"] []

def p0 : Program := { body := .skip 0, arrays := #[] }

def topState : Abs := { vars := fun _ => Interval.top, mem := fun _ => Interval.top }

def valid : Certificate D.Abs :=
  Certificate.ofSparse 1 2
    { point := 0, label := 0, state := some topState }
    []

#guard valid.wellFormed p0
#guard (check D p0 valid).isOk

/-! ## Lookup defaults -/

def withBot : Certificate D.Abs :=
  Certificate.ofSparse 1 2
    { point := 0, label := 0, state := some topState }
    [ { point := 1, label := 0, state := none } ]

#guard (Certificate.stateAt D withBot 1 0).isNone
#guard (Certificate.stateAt D withBot 5 0).isSome
#guard (Certificate.entryAt valid).isSome
#guard (Certificate.entryAt withBot).isSome

/-! ## Structural failures -/

def badLabels : Certificate D.Abs :=
  { valid with labels := 0 }

def badEntryPoint : Certificate D.Abs :=
  { valid with entry := { point := 1, label := 0, state := some topState } }

def badEntryLabel : Certificate D.Abs :=
  { valid with entry := { point := 0, label := 1, state := some topState } }

def badSize : Certificate D.Abs :=
  { valid with states := #[] }

def entryRepeated : Certificate D.Abs :=
  Certificate.ofSparse 1 2
    { point := 0, label := 0, state := some topState }
    [ { point := 0, label := 0, state := some topState } ]

def haltState : Certificate D.Abs :=
  Certificate.ofSparse 1 2
    { point := 0, label := 0, state := some topState }
    [ { point := 1, label := 0, state := some topState } ]

#guard !badLabels.wellFormed p0
#guard !badEntryPoint.wellFormed p0
#guard !badEntryLabel.wellFormed p0
#guard !badSize.wellFormed p0
#guard !entryRepeated.wellFormed p0

-- v1 §3.1: the halt point carries no certificate state.
#guard !haltState.wellFormed p0
#guard !(check D p0 haltState).isOk

#guard !(check D p0 badLabels).isOk
#guard (match check D p0 badEntryPoint with
  | .error d => d.kind = .malformed
  | .ok _ => false)

-- A non-WF source program is rejected before certificate validation.
def pNonWF : Program :=
  { body := .ite 0 (.cmp .lt (.var "x") (.const (I32.ofIntWrap 3)))
      (.skip 1) (.skip 2),
    arrays := #[] }

#guard !pNonWF.checkWF
#guard !(check D pNonWF valid).isOk
#guard (match check D pNonWF valid with
  | .error d => d.kind = .malformed
  | .ok _ => false)