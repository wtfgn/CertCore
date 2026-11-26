import CertCore.Domain.IntervalInstance

/-!
# Interval unit tests (M2.9)

Run with:

    lake env lean lean/Tests/IntervalUnit.lean

Ten hand-computed cases, one per core operation. Every check is a `#guard`, so a
wrong answer fails the build rather than merely printing.
-/

open CertCore

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

/-! 1. A singleton contains its point and nothing else. -/
example : Interval.gamma (Interval.toInterval (c 5)) (c 5) :=
  Interval.gamma_toInterval (c 5)

example : ¬ Interval.gamma (Interval.toInterval (c 5)) (c 4) := by
  intro h
  have h' : c 4 = c 5 := Interval.gamma_toInterval_iff.1 h
  exact absurd h' (by decide)

/-! 2. `[2,8]` is included in `[0,10]`, not the other way round. -/
#guard Interval.ble (between 2 8) (between 0 10)
#guard !Interval.ble (between 0 10) (between 2 8)

/-! 3. The convex hull of `[0,1]` and `[3,4]` is `[0,4]`. -/
#guard Interval.join (between 0 1) (between 3 4) = between 0 4

/-! 4. Every value and every tested interval is inside `top`. -/
example : Interval.gamma Interval.top (c 42) := Interval.top_sound (c 42)
#guard Interval.ble (between (-100) 100) Interval.top

/-! 5. `[1,2] + [3,4] = [4,6]`. -/
#guard Interval.add (between 1 2) (between 3 4) = between 4 6

/-! 6. `[1,2] - [3,4] = [-3,-1]`. -/
#guard Interval.sub (between 1 2) (between 3 4) = between (-3) (-1)

/-! 7. `max + 1` overflows and collapses to `top`. -/
def maxEnv : Interval.Env := fun _ => Interval.toInterval I32.max
#guard Interval.evalExpr maxEnv (.add (.var "x") (.const I32.one)) = Interval.top

/-! 8. An array read returns the array interval. -/
def lengths : Arr → Nat := fun a => if a = 0 then 2 else 0
def abs : Interval.Abs :=
  { vars := fun _ => Interval.top,
    mem := fun a => if a = 0 then between 10 20 else Interval.top }
#guard Interval.evalExprAbs lengths abs (.read 0 (.const (c 0))) = between 10 20

/-! 9. `len` of an array of length 2 is `[2,2]`. -/
#guard Interval.evalExprAbs lengths abs (.len 0) = Interval.toInterval (c 2)

/-! 10. Bounds: `[0,1]` is inside length 2, `[0,2]` is not. -/
#guard Interval.idxWithin (between 0 1) 2
#guard !Interval.idxWithin (between 0 2) 2
