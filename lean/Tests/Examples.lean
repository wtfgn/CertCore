import CertCore.Semantics

/-!
# M1.11 example programs

The Lean encodings of the three `examples/*.imp` fixtures, with their expected
`run` outcomes pinned. Run with:

    lake env lean lean/Tests/Examples.lean

Point assignment follows the convention in `docs/imp-syntax.md`: source pre-order
for atomic and branch commands, starting at 0, plus one halt point.

  - `examples/safe.imp`            reaches halt with `x = 3`, `y = 1`
  - `examples/div-zero.imp`        fails at `y := 10 / x` with `x = 0`
  - `examples/array-overflow.imp`  fails storing `a[3]` in an array of length 3
-/

open CertCore
open CertCore.CFG

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

def pointOf (o : Option (Point × State)) : Option Point := o.map (fun r => r.1)
def varOf (o : Option (Point × State)) (x : Var) : Option I32 := o.map (fun r => r.2.get x)

/-- Left-to-right sequencing of a first command and a list of followers. -/
def chain : Cmd → List Cmd → Cmd
  | c, [] => c
  | c, d :: ds => .seq c (chain d ds)

/-! ## `safe.imp` -/

def safeProg : Program where
  body :=
    chain (.assign 0 "x" (.const (c 0)))
      [ .assign 1 "y" (.const (c 1)),
        .while 2 (.cmp .lt (.var "x") (.const (c 3)))
          (.assign 3 "x" (.add (.var "x") (.const (c 1)))),
        .assert 4 (.cmp .eq (.var "x") (.const (c 3))) ]
  arrays := #[]

def safeCfg : CFG := Program.compile safeProg
def safeSt : State := State.init safeProg

-- Three loop iterations, the guard fails, the assert holds, then halt.
#guard safeCfg.entry = 0
#guard pointOf (run safeCfg 10 safeCfg.entry safeSt) = some 5
#guard varOf (run safeCfg 10 safeCfg.entry safeSt) "x" = some (c 3)
#guard varOf (run safeCfg 10 safeCfg.entry safeSt) "y" = some (c 1)

-- The halt stutter keeps the result stable under more fuel.
#guard pointOf (run safeCfg 100 safeCfg.entry safeSt) = some 5
#guard varOf (run safeCfg 100 safeCfg.entry safeSt) "x" = some (c 3)

/-! ## `div-zero.imp` -/

def divProg : Program where
  body :=
    chain (.assign 0 "x" (.const (c 0)))
      [ .assign 1 "y" (.div (.const (c 10)) (.var "x")) ]
  arrays := #[]

def divCfg : CFG := Program.compile divProg
def divSt : State := State.init divProg

-- One step initialises x; the next step divides by zero and fails.
#guard pointOf (run divCfg 1 divCfg.entry divSt) = some 1
#guard (run divCfg 2 divCfg.entry divSt).isNone
#guard (step divCfg 1 divSt).isNone

/-! ## `array-overflow.imp` -/

def arrProg : Program where
  body :=
    chain (.assign 0 "i" (.const (c 3)))
      [ .store 1 0 (.var "i") (.const (c 1)) ]
  arrays := #[3]

def arrCfg : CFG := Program.compile arrProg
def arrSt : State := State.init arrProg

-- One step sets i = 3; storing a[3] in an array of length 3 fails.
#guard pointOf (run arrCfg 1 arrCfg.entry arrSt) = some 1
#guard (run arrCfg 2 arrCfg.entry arrSt).isNone
#guard (step arrCfg 1 (arrSt.set "i" (c 3))).isNone

/-! ## The fixtures satisfy source well-formedness -/

#guard safeProg.checkWF
#guard divProg.checkWF
#guard arrProg.checkWF
#guard (Program.compileChecked safeProg).isSome
