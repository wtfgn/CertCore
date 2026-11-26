import CertCore.Domain.IntervalTransfer

/-!
# Arithmetic transfer smoke tests (M2.6)

Run with:

    lake env lean lean/Tests/Transfer.lean

Pins constants/variables/`+`/`-`, the overflow-to-top policy, the conservative
`*`/`/`/array/`len` cases, and concrete uses of `evalExpr_sound`/`assign_sound`.
-/

open CertCore

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

/-- x ∈ [1,2], y ∈ [3,4], everything else is `bot`. -/
def env : Interval.Env := fun v =>
  if v = "x" then between 1 2
  else if v = "y" then between 3 4
  else Interval.bot

def x : Expr := .var "x"
def y : Expr := .var "y"

/-! ## Constants, variables and arithmetic -/

#guard Interval.evalExpr env (.const (c 5)) = Interval.toInterval (c 5)
#guard Interval.evalExpr env x = between 1 2
#guard Interval.evalExpr env (.add x y) = between 4 6
#guard Interval.evalExpr env (.sub x y) = between (-3) (-1)
#guard Interval.evalExpr env (.add x (.const (c 10))) = between 11 12
#guard Interval.evalExpr env (.sub (.const (c 0)) y) = between (-4) (-3)

/-! ## Overflow collapses to top -/

def maxEnv : Interval.Env := fun _ => Interval.toInterval I32.max
def minEnv : Interval.Env := fun _ => Interval.toInterval I32.min

#guard Interval.evalExpr maxEnv (.add x (.const I32.one)) = Interval.top
#guard Interval.evalExpr minEnv (.sub x (.const I32.one)) = Interval.top

/-! ## Conservative cases -/

#guard Interval.evalExpr env (.mul x y) = Interval.top
#guard Interval.evalExpr env (.div x y) = Interval.top
#guard Interval.evalExpr env (.read 0 (.const (c 0))) = Interval.top
#guard Interval.evalExpr env (.len 0) = Interval.top

/-! ## `evalExpr_sound` and `assign_sound` -/

def concrete : State :=
  { env := fun v =>
      if v = "x" then c 1
      else if v = "y" then c 3
      else c 0,
    mem := fun _ => #[] }

def concreteEnv : Interval.Env := fun v =>
  if v = "x" then Interval.toInterval (c 1)
  else if v = "y" then Interval.toInterval (c 3)
  else Interval.top

example : Interval.gamma (Interval.evalExpr concreteEnv (.add x y)) (c 4) := by
  apply Interval.evalExpr_sound (s := concrete) (e := .add x y) (v := c 4)
  · intro v
    by_cases hx : v = "x"
    · subst v
      simp [concreteEnv, concrete, State.get, Interval.gamma_toInterval]
    · by_cases hy : v = "y"
      · subst v
        simp [concreteEnv, concrete, State.get, Interval.gamma_toInterval]
      · simp [concreteEnv, concrete, State.get, hx, hy, Interval.top_sound]
  · decide

example : Interval.gamma (Interval.assign concreteEnv "z" (.const (c 5)) "z")
    ((concrete.set "z" (c 5)).get "z") := by
  apply Interval.assign_sound (env := concreteEnv) (s := concrete)
    (x := "z") (e := .const (c 5)) (v := c 5)
  · intro v
    by_cases hx : v = "x"
    · subst v
      simp [concreteEnv, concrete, State.get, Interval.gamma_toInterval]
    · by_cases hy : v = "y"
      · subst v
        simp [concreteEnv, concrete, State.get, Interval.gamma_toInterval]
      · simp [concreteEnv, concrete, State.get, hx, hy, Interval.top_sound]
  · simp [eval]
