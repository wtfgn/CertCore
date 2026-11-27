import CertCore.Check
import CertCore.Domain.IntervalInstance

/-!
# Edge-obligation tests (M3.5)

Run with:

    lake env lean lean/Tests/CheckEdges.lean

The edge family is `ble (transfer c (at src)) (at dst)` for every compiled edge
and every label, with missing targets `⊤` and explicit `bot` targets rejected.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def D : CertDomain := intervalDomain (fun _ => 0) ["x"] []

def st (n : Int) : Interval.Abs :=
  { vars := fun v => if v = "x" then Interval.toInterval (c n) else Interval.top,
    mem := fun _ => Interval.top }

def pAssign : Program :=
  { body := .assign 0 "x" (.const (c 1)), arrays := #[] }

def pSkip : Program := { body := .skip 0, arrays := #[] }

def goodEntry : StateAt D.Abs :=
  { point := 0, label := 0, state := some (D.initOf pAssign) }

def certWith (target : Option D.Abs) : Certificate D.Abs :=
  { labels := 1,
    entry := goodEntry,
    states := [ { point := 1, label := 0, state := target } ] }

def okTarget : Certificate D.Abs := certWith (some (st 1))
def badTarget : Certificate D.Abs := certWith (some (st 2))
def botTarget : Certificate D.Abs := certWith none

#guard okTarget.wellFormed pAssign
#guard (check D pAssign okTarget).isOk

-- `x := 1` transfers `[0,0]` to `[1,1]`; claiming `[2,2]` at the target fails.
#guard !(check D pAssign badTarget).isOk

-- A reachable edge into an explicit `bot` state fails.
#guard !(check D pAssign botTarget).isOk

-- The failure is a typed edge diagnostic naming the edge and label.
#guard (match check D pAssign badTarget with
  | .error d =>
      decide (d.kind = .edge) && d.edge.isSome && decide (d.point = some 0) &&
      decide (d.label = some 0) && d.expected.isSome && d.actual.isSome
  | .ok _ => false)

#guard (match check D pAssign botTarget with
  | .error d => decide (d.kind = .edge) && d.edge.isSome && d.actual.isNone
  | .ok _ => false)

-- A missing target is `top`, so the edge obligation passes.
def missingCert : Certificate D.Abs :=
  { labels := 1, entry := goodEntry, states := [] }
#guard (check D pAssign missingCert).isOk

-- Multiple labels use the identity update at M3.5; both labels are checked.
def twoLabels : Certificate D.Abs :=
  { labels := 2,
    entry := goodEntry,
    states :=
      [ { point := 1, label := 0, state := some (st 1) },
        { point := 1, label := 1, state := some (st 2) } ] }

#guard twoLabels.wellFormed pAssign
#guard !(check D pAssign twoLabels).isOk

-- A non-overwriting entry instruction must use the certificate's `entry` state,
-- not the sparse-map default (`top`) at the entry key.
def skipCert : Certificate D.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some (D.initOf pSkip) },
    states := [ { point := 1, label := 0, state := some (D.initOf pSkip) } ] }

#guard skipCert.wellFormed pSkip
#guard (check D pSkip skipCert).isOk