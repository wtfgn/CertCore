import CertCore.Domain.IntervalInstance

/-!
# Showcase demos (F3)

Run with:

    lake env lean lean/Tests/Demo.lean

Two certificate tables that the M2 review said the domain could not yet certify:

* `examples/safe.imp`: the loop `x := 0; while (x < 3) { x := x + 1 }; assert (x == 3)`
  with the head invariant `x ∈ [0,3]`. The guard refinement sharpens the body
  entry to `[0,2]`, the body exit to `[1,3]` (inside the head), and the exit edge
  to `[3,3]`, where the assert holds.
* `docs/certificate-v1.md` §13: `x := 0; x := x + 1; y := 10 / x; assert (y == 10)`.
  The singleton division transfers `10 / [1,1]` to `[10,10]`, so the edge and the
  assert both check.

Every statement is a `#guard`, so a regression fails the build.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

/-- No arrays; `x` and `y` are the only variables. -/
def lengths0 : Arr → Nat := fun _ => 0

def D : CertDomain := intervalDomain lengths0 ["x", "y"] []

def state2 (xlo xhi ylo yhi : Int) : Abs :=
  { vars := fun v =>
      if v = "x" then between xlo xhi
      else if v = "y" then between ylo yhi
      else Interval.top,
    mem := fun _ => Interval.top }

/-! ## `examples/safe.imp`: guard refinement closes the loop -/

def guardLt : BExp := .cmp .lt (.var "x") (.const (c 3))

/-- Head invariant `x ∈ [0,3]`, `y ∈ top`. -/
def head : Abs :=
  { vars := fun v => if v = "x" then between 0 3 else Interval.top,
    mem := fun _ => Interval.top }

-- True edge: `x < 3` sharpens the body entry to `[0,2]`.
#guard (D.transfer (.assume guardLt true) head).vars "x" = between 0 2

-- The body `x := x + 1` then gives `[1,3]`, which is inside the head `[0,3]`.
def bodyExit : Abs :=
  D.transfer (.atomic (.assign "x" (.add (.var "x") (.const (c 1)))))
    (D.transfer (.assume guardLt true) head)

#guard bodyExit.vars "x" = between 1 3
#guard D.ble bodyExit head

-- False edge: `x < 3` is false, so `x >= 3`; with `x <= 3` this is `[3,3]`.
def exitState : Abs := D.transfer (.assume guardLt false) head

#guard exitState.vars "x" = between 3 3
#guard D.entails exitState (.cmp .eq (.var "x") (.const (c 3)))

-- The swapped form `3 > x` refines the same way.
#guard (D.transfer (.assume (.cmp .gt (.const (c 3)) (.var "x")) true) head).vars "x" =
  between 0 2

/-! ## certificate-v1 §13: singleton division -/

def divExpr : Expr := .div (.const (c 10)) (.var "x")

def s2 : Abs := state2 1 1 0 0  -- x = 1, y unconstrained
def s3 : Abs := state2 1 1 10 10 -- x = 1, y = 10

def transferred : Abs := D.transfer (.atomic (.assign "y" divExpr)) s2

#guard transferred.vars "y" = between 10 10
#guard D.ble transferred s3

-- The two safety obligations at the division point.
#guard D.entails s2 (.cmp .ne (.var "x") (.const (c 0)))

def divSafe (dividend : Expr) : BExp :=
  .not (.and (.cmp .eq dividend (.const I32.min))
             (.cmp .eq (.var "x") (.const (c (-1)))))

#guard D.entails s2 (divSafe (.const (c 10)))

-- The assert at point 3.
#guard D.entails s3 (.cmp .eq (.var "y") (.const (c 10)))
