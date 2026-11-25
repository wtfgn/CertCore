import CertCore.Semantics

/-!
# `edges` smoke tests

Build-time checks of the M1.8 projection. Run with:

    lake env lean lean/Tests/Edges.lean

Pins the exact edge list of the running example — ascending point order, one edge
per atomic instruction, guard-true before guard-false for a branch, and the halt
self-loop — and checks that the membership lemmas agree with the enumeration.
-/

open CertCore

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

/-- The expected projection: points 0..3 plus the halt edge at 4. -/
def expected : List Edge :=
  [ { src := 0, cmd := .atomic (.assign "x" (.const (c 0))), dst := 1 },
    { src := 1, cmd := .assume (.cmp .lt (.var "x") (.const (c 2))) true, dst := 2 },
    { src := 1, cmd := .assume (.cmp .lt (.var "x") (.const (c 2))) false, dst := 3 },
    { src := 2, cmd := .atomic (.assign "x" (.add (.var "x") (.const (c 1)))), dst := 1 },
    { src := 3, cmd := .atomic (.assert (.cmp .eq (.var "x") (.const (c 2)))), dst := 4 },
    { src := 4, cmd := .atomic .skip, dst := 4 } ]

#guard cfg.edges = expected
#guard cfg.edges.length = 6

-- The membership lemmas agree with the enumeration.
example : ({ src := 0, cmd := .atomic (.assign "x" (.const (c 0))), dst := 1 } : Edge) ∈ cfg.edges := by
  apply CFG.mem_edges_atomic
  decide

example : ({ src := 1, cmd := .assume (.cmp .lt (.var "x") (.const (c 2))) true, dst := 2 } : Edge) ∈ cfg.edges := by
  have h : cfg.instrAt 1 = some (.branch (.cmp .lt (.var "x") (.const (c 2))) 2 3) := by
    decide
  exact CFG.mem_edges_branch_true h

-- A straight-line program still gets its halt edge.
def divProg : Program :=
  { body := .assign 0 "y" (.div (.const (c 10)) (.var "x")), arrays := #[] }

#guard (Program.compile divProg).edges.length = 2

/-! ## F4 — every successful step is one edge of the graph -/

def st : State := State.init sample

#guard (EdgeCmd.exec (.atomic .skip) st).isSome
#guard (EdgeCmd.exec (.assume (.cmp .lt (.const (c 0)) (.const (c 1))) true) st).isSome
#guard (EdgeCmd.exec (.assume (.cmp .lt (.const (c 0)) (.const (c 1))) false) st).isNone

-- The guard-true branch at point 1 goes to 2, and the edge effect leaves the
-- state unchanged; `step_edge` finds exactly that edge.
example : ∃ e ∈ cfg.edges, e.src = 1 ∧ e.dst = 2 ∧ e.cmd.exec st = some st :=
  CFG.step_edge (cfg := cfg) (p := 1) (s := st) (q := 2) (s' := st) rfl

-- The guard-false branch goes to 3 with x = 2.
example : ∃ e ∈ cfg.edges, e.src = 1 ∧ e.dst = 3 ∧
    e.cmd.exec (st.set "x" (c 2)) = some (st.set "x" (c 2)) :=
  CFG.step_edge (cfg := cfg) (p := 1) (s := st.set "x" (c 2))
    (q := 3) (s' := st.set "x" (c 2)) rfl

-- An atomic `skip` also projects to its edge.
def skipProg : Program := { body := .skip 0, arrays := #[] }
def skipCfg : CFG := Program.compile skipProg

example : ∃ e ∈ skipCfg.edges, e.src = 0 ∧ e.dst = 1 ∧
    e.cmd.exec (State.init skipProg) = some (State.init skipProg) :=
  CFG.step_edge (cfg := skipCfg) (p := 0) (s := State.init skipProg)
    (q := 1) (s' := State.init skipProg) rfl
