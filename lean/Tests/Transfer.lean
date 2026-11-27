import CertCore.Domain.IntervalInstance

/-!
# Arithmetic transfer smoke tests (M2.6/F6)

Run with:

    lake env lean lean/Tests/Transfer.lean

The final transfer is the support-restricted `evalExprAbsOn`/`assignAbsOn` in
`IntervalInstance`; the M2.6 `Env` evaluator was removed at F6 so there is one
trusted transfer on the path. This file pins constants/variables/`+`/`-`, the
overflow-to-top policy, the conservative `*`/`/`/array/`len` cases, and concrete
uses of `evalExprAbsOn_sound`/`assignAbsOn_sound`.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

def lengths0 : Arr → Nat := fun _ => 0

def vars : List Var := ["x", "y"]

/-- `x ∈ [1,2]`, `y ∈ [3,4]`, everything else is `top` outside the support. -/
def abs : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then between 1 2
      else if v = "y" then between 3 4
      else Interval.bot,
    mem := fun _ => Interval.top }

def x : Expr := .var "x"
def y : Expr := .var "y"

def evalOn (e : Expr) : Interval := evalExprAbsOn lengths0 vars [] abs e

/-! ## Constants, variables and arithmetic -/

#guard evalOn (.const (c 5)) = Interval.toInterval (c 5)
#guard evalOn x = between 1 2
#guard evalOn (.add x y) = between 4 6
#guard evalOn (.sub x y) = between (-3) (-1)
#guard evalOn (.add x (.const (c 10))) = between 11 12
#guard evalOn (.sub (.const (c 0)) y) = between (-4) (-3)

/-! ## Overflow collapses to top -/

def maxAbs : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then Interval.toInterval I32.max
      else if v = "y" then Interval.toInterval I32.max
      else Interval.top,
    mem := fun _ => Interval.top }

def minAbs : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then Interval.toInterval I32.min
      else if v = "y" then Interval.toInterval I32.min
      else Interval.top,
    mem := fun _ => Interval.top }

#guard evalExprAbsOn lengths0 vars [] maxAbs (.add x (.const I32.one)) = Interval.top
#guard evalExprAbsOn lengths0 vars [] minAbs (.sub x (.const I32.one)) = Interval.top

/-! ## Conservative cases -/

#guard evalOn (.mul x y) = Interval.top
#guard evalOn (.div x y) = Interval.top
#guard evalOn (.read 0 (.const (c 0))) = Interval.top
#guard evalOn (.len 0) = Interval.top

/-! ## `evalExprAbsOn_sound` and `assignAbsOn_sound` -/

def concrete : State :=
  { env := fun v =>
      if v = "x" then c 1
      else if v = "y" then c 3
      else c 0,
    mem := fun _ => #[] }

/-- The same boxes, but singletons matching `concrete`. -/
def absConcrete : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then Interval.toInterval (c 1)
      else if v = "y" then Interval.toInterval (c 3)
      else Interval.top,
    mem := fun _ => Interval.top }

theorem concreteSound : GammaOn lengths0 vars [] absConcrete concrete := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    by_cases hx : v = "x"
    · subst v
      simp [absConcrete, concrete, State.get, gamma_toInterval]
    · by_cases hy : v = "y"
      · subst v
        simp [absConcrete, concrete, State.get, gamma_toInterval]
      · simp [vars, hx, hy] at hv
  · intro a ha
    simp at ha
  · intro a ha
    simp at ha

example : Interval.gamma
    (evalExprAbsOn lengths0 vars [] absConcrete (.add x y)) (c 4) := by
  apply evalExprAbsOn_sound (e := .add x y) (v := c 4) concreteSound
  decide

example : Interval.gamma
    ((assignAbsOn lengths0 vars [] absConcrete "x" (.const (c 5))).vars "x")
    ((concrete.set "x" (c 5)).get "x") := by
  have h := assignAbsOn_sound (x := "x") (e := .const (c 5)) (v := c 5)
    concreteSound (by decide : eval (.const (c 5)) concrete = some (c 5))
  exact h.1 "x" (by simp [vars])
