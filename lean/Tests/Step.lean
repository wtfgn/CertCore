import CertCore.Semantics

/-!
# `compile` / `step` smoke tests

Build-time checks of the M1.6 edge machine. Run with:

    lake env lean lean/Tests/Step.lean

Pins the compiled shape of the running example (one instruction per point plus a
halt slot), branch selection, the halt stutter, and each way a step can fail:
failed assignment evaluation, failed assertion, out-of-bounds store, failing
guard, and an out-of-range point. `step` is compared through projections because
`State` is a pair of functions and has no decidable equality.
-/

open CertCore
open CertCore.CFG

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-- `0: x := 0; 1: while (x < 2) { 2: x := x+1 }; 3: assert (x == 2)`. -/
def sample : Program where
  body :=
    .seq (.assign 0 "x" (.const (c 0)))
      (.seq (.while 1 (.cmp .lt (.var "x") (.const (c 2)))
              (.assign 2 "x" (.add (.var "x") (.const (c 1)))))
            (.assert 3 (.cmp .eq (.var "x") (.const (c 2)))))
  arrays := #[]

def cfg : CFG := Program.compile sample
def st : State := State.init sample

def pointOf (o : Option (Point × State)) : Option Point := o.map (fun r => r.1)
def varOf (o : Option (Point × State)) (x : Var) : Option I32 := o.map (fun r => r.2.get x)

-- Compilation: entry 0, points 0..3, halt slot at 4.
#guard cfg.entry = 0
#guard cfg.instrs.size = 5

-- 0: x := 0, then to the guard.
#guard pointOf (step cfg 0 st) = some 1
#guard varOf (step cfg 0 st) "x" = some (c 0)

-- 1: x < 2 is true, so enter the body.
#guard pointOf (step cfg 1 st) = some 2

-- 2: increment, then back to the guard.
#guard pointOf (step cfg 2 st) = some 1
#guard varOf (step cfg 2 st) "x" = some (c 1)

-- 1: x < 2 is false, so leave the loop.
#guard pointOf (step cfg 1 (st.set "x" (c 2))) = some 3

-- 3: the assertion holds, then halt.
#guard pointOf (step cfg 3 (st.set "x" (c 2))) = some 4

-- The halt point stutters rather than failing.
#guard pointOf (step cfg 4 st) = some 4

-- A failed assignment evaluation is a step failure.
def divProg : Program :=
  { body := .assign 0 "y" (.div (.const (c 10)) (.var "x")), arrays := #[] }
#guard (step (Program.compile divProg) 0 st).isNone

-- A failed assertion is a step failure.
def assertProg : Program :=
  { body := .assert 0 (.cmp .eq (.var "x") (.const (c 1))), arrays := #[] }
#guard (step (Program.compile assertProg) 0 st).isNone

-- An out-of-bounds store is a step failure (array 0 has length 0 here).
def storeProg : Program :=
  { body := .store 0 0 (.const (c 0)) (.const (c 1)), arrays := #[] }
#guard (step (Program.compile storeProg) 0 st).isNone

-- A failing condition is a step failure (10 / x with x = 0).
def guardProg : Program :=
  { body := .ite 0 (.cmp .gt (.div (.const (c 10)) (.var "x")) (.const (c 0)))
      (.skip 1) (.skip 2),
    arrays := #[] }
#guard (step (Program.compile guardProg) 0 st).isNone

-- A point outside the instruction array is a lookup failure, not a hazard.
#guard (step (Program.compile divProg) 99 st).isNone

-- An in-bounds store succeeds and writes the cell.
def storeOk : Program :=
  { body := .store 0 0 (.const (c 1)) (.const (c 42)), arrays := #[3] }
def stOk : State := State.init storeOk
#guard pointOf (step (Program.compile storeOk) 0 stOk) = some 1
#guard (step (Program.compile storeOk) 0 stOk).map
         (fun r => (r.2.memAt 0).getD 1 I32.zero) = some (c 42)
