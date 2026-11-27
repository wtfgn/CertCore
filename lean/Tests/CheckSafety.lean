import CertCore.Check
import CertCore.Domain.IntervalInstance

/-!
# Safety-obligation tests (M3.6)

Run with:

    lake env lean lean/Tests/CheckSafety.lean

Covers assert truth, division definedness/overflow, branch definedness, array
index bounds, and the typed safety diagnostic.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def D : CertDomain := intervalDomain (fun _ => 0) ["x"] []

def D2 : CertDomain := intervalDomain (fun _ => 0) ["x", "y"] []

def DArr : CertDomain :=
  intervalDomain (fun a => if a = 0 then 2 else 0) ["i"] [0]

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

def st1 (n : Int) : Interval.Abs :=
  { vars := fun v => if v = "x" then Interval.toInterval (c n) else Interval.top,
    mem := fun _ => Interval.top }

def st2 (xl xh yl yh : Int) : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then between xl xh
      else if v = "y" then between yl yh
      else Interval.top,
    mem := fun _ => Interval.top }

def stI (lo hi : Int) : Interval.Abs :=
  { vars := fun v => if v = "i" then between lo hi else Interval.top,
    mem := fun _ => Interval.top }

/-! ## Assert truth -/

def pAssert : Program :=
  { body := .seq (.assign 0 "x" (.const (c 1)))
      (.assert 1 (.cmp .eq (.var "x") (.const (c 1)))),
    arrays := #[] }

def pAssertBad : Program :=
  { body := .seq (.assign 0 "x" (.const (c 1)))
      (.assert 1 (.cmp .eq (.var "x") (.const (c 2)))),
    arrays := #[] }

def assertCert (p : Program) : Certificate D.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some (D.initOf p) },
    states := [ { point := 1, label := 0, state := some (st1 1) } ] }

#guard (check D pAssert (assertCert pAssert)).isOk
#guard !(check D pAssertBad (assertCert pAssertBad)).isOk

#guard (match check D pAssertBad (assertCert pAssertBad) with
  | .error d => decide (d.kind = .safety) && decide (d.point = some 1)
  | .ok _ => false)

/-! ## Division safety -/

def pDiv : Program :=
  { body := .seq (.assign 0 "x" (.const (c 1)))
      (.seq (.assign 1 "y" (.div (.const (c 10)) (.var "x")))
        (.assert 2 (.cmp .eq (.var "y") (.const (c 10))))),
    arrays := #[] }

def divCert (xl xh : Int) : Certificate D2.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some (D2.initOf pDiv) },
    states :=
      [ { point := 1, label := 0, state := some (st2 xl xh 0 0) },
        { point := 2, label := 0, state := some (st2 1 1 10 10) } ] }

#guard (check D2 pDiv (divCert 1 1)).isOk
#guard !(check D2 pDiv (divCert (-1) 1)).isOk

-- Direct guarded-entailment checks for a division guard and overflow.
def divGuard : BExp := .cmp .lt (.div (.const (c 10)) (.var "x")) (.const (c 3))

#guard D.entails (st1 1) (instrSafe (.branch divGuard 1 2))
#guard !D.entails (st1 0) (instrSafe (.branch divGuard 1 2))

def addOverflow : Instr :=
  .atomic (.assign "x" (.add (.var "x") (.const (c 1)))) 1

#guard D.entails (st1 0) (instrSafe addOverflow)
#guard !D.entails (st1 2147483647) (instrSafe addOverflow)

/-! ## Branch definedness -/

def pBranch : Program :=
  { body := .seq (.assign 0 "x" (.const (c 0)))
      (.ite 1 (.cmp .lt (.var "x") (.const (c 3))) (.skip 2) (.skip 3)),
    arrays := #[] }

def branchAbs : Interval.Abs :=
  { vars := fun v => if v = "x" then between 0 10 else Interval.top,
    mem := fun _ => Interval.top }

def branchCert : Certificate D.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some (D.initOf pBranch) },
    states := [ { point := 1, label := 0, state := some branchAbs } ] }

#guard (check D pBranch branchCert).isOk

/-! ## Array index bounds -/

def pStore : Program :=
  { body := .seq (.assign 0 "i" (.const (c 0)))
      (.store 1 0 (.var "i") (.const (c 1))),
    arrays := #[2] }

def storeCert (lo hi : Int) : Certificate DArr.Abs :=
  { labels := 1,
    entry := { point := 0, label := 0, state := some (DArr.initOf pStore) },
    states := [ { point := 1, label := 0, state := some (stI lo hi) } ] }

#guard (check DArr pStore (storeCert 0 1)).isOk
#guard !(check DArr pStore (storeCert 0 2)).isOk
