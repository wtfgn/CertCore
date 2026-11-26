import CertCore.Semantics

/-!
# `compile` / `WF` regression tests

Build-time checks for the F1/F2/F7 fixes:

* `Cmd.maxPoint` must include `if`/`while` bodies, so the instruction array is
  large enough for every point;
* `Program.compile_wf` must hold for branch-tail, loop-tail, straight-line and
  nested programs;
* `Program.checkWF` must reject duplicate points, undeclared arrays, unbound
  reads, and an oversized `maxPoint`; `compileChecked` must return `none` for
  those programs;
* the branch-tail bodies must actually be present and reachable.

Run with:

    lake env lean lean/Tests/Compile.lean

Everything is a `#guard` or an `example` checked at elaboration time, so a
regression fails the build.
-/

open CertCore
open CertCore.CFG

/-- In-range test constant. -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-- A condition that is true from the initial state. -/
def b : BExp := .cmp .lt (.const (c 0)) (.const (c 1))

/-- The loop body is the highest-numbered point; a shallow `maxPoint` truncates it. -/
def loopTail : Program :=
  { body := .while 0 b (.seq (.skip 1) (.assign 2 "x" (.const (c 1)))),
    arrays := #[] }

/-- Both `if` branches are the highest-numbered points. -/
def ifTail : Program :=
  { body := .ite 0 b (.skip 1) (.skip 2), arrays := #[] }

/-- Straight-line control; the halt slot is the only extra point. -/
def straight : Program :=
  { body := .assign 0 "x" (.const (c 1)), arrays := #[] }

/-- A nested branch inside a loop, followed by nothing. -/
def nested : Program :=
  { body := .seq (.skip 0) (.while 1 b (.ite 2 b (.skip 3) (.skip 4))),
    arrays := #[] }

def loopCfg : CFG := Program.compile loopTail
def ifCfg : CFG := Program.compile ifTail
def straightCfg : CFG := Program.compile straight
def nestedCfg : CFG := Program.compile nested

def pointOf (o : Option (Point × State)) : Option Point := o.map (fun r => r.1)

/-! ## Source well-formedness (`Program.checkWF`) -/

/-- Duplicate points: the second write would overwrite the first. -/
def duplicatePoints : Program :=
  { body := .seq (.skip 0) (.skip 0), arrays := #[] }

/-- A non-dense point list: point 1 is missing. -/
def gapPoints : Program :=
  { body := .seq (.skip 0) (.skip 2), arrays := #[] }

/-- An array index outside `Program.arrays`. -/
def badArray : Program :=
  { body := .store 0 1 (.const (c 0)) (.const (c 1)), arrays := #[] }

/-- A read of a variable that is never assigned. -/
def unboundRead : Program :=
  { body := .assert 0 (.cmp .eq (.var "x") (.const (c 0))), arrays := #[] }

/-- A point beyond the frontend's allocation bound. -/
def tooManyPoints : Program :=
  { body := .skip (maxProgramPoints + 1), arrays := #[] }

#guard loopTail.checkWF
#guard ifTail.checkWF
#guard straight.checkWF
#guard nested.checkWF

#guard !duplicatePoints.checkWF
#guard !gapPoints.checkWF
#guard !badArray.checkWF
#guard !unboundRead.checkWF
#guard !tooManyPoints.checkWF

example : straight.WF := by
  unfold Program.WF
  decide
example : (Program.compileChecked straight).isSome := by decide
example : (Program.compileChecked ifTail).isSome := by decide
example : (Program.compileChecked duplicatePoints).isNone := by decide
example : (Program.compileChecked gapPoints).isNone := by decide
example : (Program.compileChecked badArray).isNone := by decide
example : (Program.compileChecked unboundRead).isNone := by decide

example {cfg : CFG} (h : Program.compileChecked straight = some cfg) : cfg.WF :=
  Program.compileChecked_wf h

/-! ## `maxPoint` counts branch and loop bodies -/

#guard Cmd.maxPoint (.while 0 b (.skip 5)) = 5
#guard Cmd.maxPoint (.ite 0 b (.skip 5) (.skip 6)) = 6
#guard Cmd.maxPoint nested.body = 4

/-! ## Array sizes: largest point + halt + one slot -/

#guard loopCfg.instrs.size = 4
#guard ifCfg.instrs.size = 4
#guard straightCfg.instrs.size = 2
#guard nestedCfg.instrs.size = 6

/-! ## Every compiled edge lands inside the instruction array -/

#guard loopCfg.edges.all (fun e => e.dst < loopCfg.instrs.size)
#guard ifCfg.edges.all (fun e => e.dst < ifCfg.instrs.size)
#guard straightCfg.edges.all (fun e => e.dst < straightCfg.instrs.size)
#guard nestedCfg.edges.all (fun e => e.dst < nestedCfg.instrs.size)

/-! ## The branch-tail bodies are present and reachable -/

#guard loopCfg.instrAt 2 |>.isSome
#guard ifCfg.instrAt 1 |>.isSome
#guard ifCfg.instrAt 2 |>.isSome
#guard nestedCfg.instrAt 3 |>.isSome
#guard nestedCfg.instrAt 4 |>.isSome

#guard pointOf (step loopCfg 0 (State.init loopTail)) = some 1
#guard pointOf (step loopCfg 2 (State.init loopTail)) = some 0
#guard pointOf (step ifCfg 0 (State.init ifTail)) = some 1

/-! ## The well-formedness theorem is available at the expected type -/

example : loopCfg.WF := Program.compile_wf loopTail
example : ifCfg.WF := Program.compile_wf ifTail
example : straightCfg.WF := Program.compile_wf straight
example : nestedCfg.WF := Program.compile_wf nested

example : ∀ e ∈ loopCfg.edges, e.dst < loopCfg.instrs.size :=
  CFG.WF.edges_dst_lt (Program.compile_wf loopTail)
