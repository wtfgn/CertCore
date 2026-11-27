import CertCore.Check
import CertCore.Domain.IntervalInstance

/-!
# Checker skeleton tests (M3.3)

Run with:

    lake env lean lean/Tests/CheckSkeleton.lean

Pins the sparse lookup (`state` / `bot` / missing-`⊤`), the structural
certificate validation, and the total `check` skeleton. Semantic obligations are
deliberately absent at M3.3.
-/

open CertCore
open CertCore.Interval

def D : CertDomain := intervalDomain (fun _ => 0) ["x"] []

def p0 : Program := { body := .skip 0, arrays := #[] }

def topState : Abs := { vars := fun _ => Interval.top, mem := fun _ => Interval.top }

def valid : Certificate D.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some topState },
    states := [] }

#guard valid.wellFormed p0
#guard (check D p0 valid).isOk

/-! ## Lookup defaults -/

def withBot : Certificate D.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some topState },
    states := [ { point := 1, label := 0, state := none } ] }

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

def badStateLabel : Certificate D.Abs :=
  { valid with states := [ { point := 1, label := 1, state := some topState } ] }

def duplicate : Certificate D.Abs :=
  { valid with states :=
      [ { point := 1, label := 0, state := some topState },
        { point := 1, label := 0, state := some topState } ] }

def entryRepeated : Certificate D.Abs :=
  { valid with states := [ { point := 0, label := 0, state := some topState } ] }

#guard !badLabels.wellFormed p0
#guard !badEntryPoint.wellFormed p0
#guard !badEntryLabel.wellFormed p0
#guard !badStateLabel.wellFormed p0
#guard !duplicate.wellFormed p0
#guard !entryRepeated.wellFormed p0

#guard !(check D p0 badLabels).isOk
#guard (match check D p0 badEntryPoint with
  | .error d => d.kind = .malformed
  | .ok _ => false)
