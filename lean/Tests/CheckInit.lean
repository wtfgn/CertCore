import CertCore.Check
import CertCore.Domain.IntervalInstance

/-!
# Init-obligation tests (M3.4)

Run with:

    lake env lean lean/Tests/CheckInit.lean

M3 is flat-label only: the entry state at label 0 must contain `initOf p`.
An explicit `bot` entry is rejected. The all-label loop is retained for M9.
-/

open CertCore
open CertCore.Interval

def D : CertDomain := intervalDomain (fun _ => 0) ["x"] []

def p0 : Program := { body := .skip 0, arrays := #[] }

def good : Interval.Abs := D.initOf p0

def bad : Interval.Abs :=
  { vars := fun v => if v = "x" then Interval.toInterval (I32.ofIntWrap 1)
      else Interval.top,
    mem := fun _ => Interval.top }

def valid : Certificate D.Abs :=
  Certificate.ofSparse 1 2
    { point := 0, label := 0, state := some good }
    []

def badEntry : Certificate D.Abs :=
  { valid with entry := { point := 0, label := 0, state := some bad } }

def botEntry : Certificate D.Abs :=
  { valid with entry := { point := 0, label := 0, state := none } }



#guard valid.wellFormed p0
#guard (check D p0 valid).isOk

-- The initial state is `[0,0]`, not `[1,1]`.
#guard !(D.ble (D.initOf p0) bad)
#guard !(check D p0 badEntry).isOk
#guard !(check D p0 botEntry).isOk

-- The failure is a typed init diagnostic at the entry point/label.
#guard (match check D p0 badEntry with
  | .error d =>
      decide (d.kind = .init) && decide (d.point = some 0) &&
      decide (d.label = some 0) && d.expected.isSome && d.actual.isSome
  | .ok _ => false)

#guard (match check D p0 botEntry with
  | .error d => decide (d.kind = .init) && d.actual.isNone
  | .ok _ => false)
