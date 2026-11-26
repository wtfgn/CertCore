import CertCore.Semantics

/-!
# `run` / `Safe` smoke tests

Build-time checks of the M1.7 layer. Run with:

    lake env lean lean/Tests/Run.lean

Pins the fuel convention (`run 0` is the starting configuration, fuel exhaustion
is not failure), the step count through the running example, the halt stutter,
and the fact that a failing step refutes `Safe`. `Safe` itself is a quantified
proposition, so the negative example is a kernel proof rather than a `#guard`.
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

-- Zero fuel is the starting configuration, not a failure.
#guard pointOf (run cfg 0 cfg.entry st) = some 0
#guard varOf (run cfg 0 cfg.entry st) "x" = some (c 0)

-- Six steps: two loop iterations, then the guard fails and the assert runs.
#guard pointOf (run cfg 6 cfg.entry st) = some 3
#guard varOf (run cfg 6 cfg.entry st) "x" = some (c 2)

-- Seven steps reach the halt point; any further fuel stays there.
#guard pointOf (run cfg 7 cfg.entry st) = some 4
#guard pointOf (run cfg 100 cfg.entry st) = some 4
#guard varOf (run cfg 100 cfg.entry st) "x" = some (c 2)

-- A program whose first step fails is not safe.
def divProg : Program :=
  { body := .assign 0 "y" (.div (.const (c 10)) (.var "x")), arrays := #[] }

example : ¬ CFG.Safe (Program.compile divProg) st := by
  apply CFG.not_safe_of_step_none
  exact Option.isNone_iff_eq_none.mp (by decide)

-- The `isSome` characterisation of safety is the unfolding of the definition.
example : CFG.Safe cfg st ↔ ∀ n, (run cfg n cfg.entry st).isSome = true :=
  CFG.safe_iff_isSome

-- F3/R2: `Program.safe` is a program-level predicate, accessible by dot notation,
-- and it requires source well-formedness (a malformed program is never safe).
example (p : Program) : Prop := p.safe
example (p : Program) : p.safe ↔ p.WF ∧ CFG.Safe (Program.compile p) (State.init p) :=
  Iff.rfl
example (p : Program) (h : p.safe) : p.WF := h.1

/-- A non-dense point list: malformed, so not certifiably safe. -/
def gapProg : Program := { body := .seq (.skip 0) (.skip 2), arrays := #[] }

example : ¬ gapProg.safe := by
  intro h
  have hwf : gapProg.checkWF = true := h.1
  have hfalse : gapProg.checkWF = false := by decide
  rw [hfalse] at hwf
  exact absurd hwf (by decide)
