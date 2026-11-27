import CertCore.Domain.IntervalInstance

/-!
# Checker-interface tests (F1)

Run with:

    lake env lean lean/Tests/Interface.lean

Pins the four operations added to `CertDomain` for the checker:
`initOf`/`init_sound`, `entails`/`entails_sound`, and `P_step`; plus the
`Option Abs` representation of the certificate's explicit `bot` state (which is
a checker design note, not a domain field).

The `example`s are type-level: they check that the fields have the statements
the checker will use. The `#guard`s evaluate the entailment test on concrete
boxes, including the failure that made `x + 1` unprovable when the box is
`[max, max]` (the overflow case).
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

def lengths : Arr → Nat := fun a => if a = 0 then 2 else 0

/-- The interval instance used by the tests. -/
def D : CertDomain := Interval.intervalDomain lengths ["x", "i"] [0]

/-- A state with `x` and `i` boxes and an unconstrained array summary. -/
def st (xlo xhi ilo ihi : Int) : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then between xlo xhi
      else if v = "i" then between ilo ihi
      else Interval.top,
    mem := fun _ => Interval.top }

/-! ## `entails`: safety predicates -/

-- `x != 0` holds on `[1,5]` and fails on `[-1,1]` (which contains 0).
#guard D.entails (st 1 5 0 1) (.cmp .ne (.var "x") (.const (c 0)))
#guard !D.entails (st (-1) 1 0 1) (.cmp .ne (.var "x") (.const (c 0)))

-- `x == 3` holds only on the singleton `[3,3]`.
#guard D.entails (st 3 3 0 1) (.cmp .eq (.var "x") (.const (c 3)))
#guard !D.entails (st 2 4 0 1) (.cmp .eq (.var "x") (.const (c 3)))

-- Array bounds: `0 <= i && i < 2` holds on `[0,1]`, fails on `[-1,1]` and `[0,2]`.
def idxOk : BExp :=
  .and (.cmp .le (.const (c 0)) (.var "i")) (.cmp .lt (.var "i") (.const (c 2)))

#guard D.entails (st 0 0 0 1) idxOk
#guard !D.entails (st 0 0 (-1) 1) idxOk
#guard !D.entails (st 0 0 0 2) idxOk

-- `x + 1 > 0` is provable from `[0,5]`; the same predicate on `[max,max]` is
-- declined because the concrete addition may overflow.
#guard D.entails (st 0 5 0 1)
  (.cmp .gt (.add (.var "x") (.const (c 1))) (.const (c 0)))
#guard !D.entails (st 2147483647 2147483647 0 1)
  (.cmp .gt (.add (.var "x") (.const (c 1))) (.const (c 0)))

-- Division overflow safety: `not (dividend = min && divisor = -1)`. With
-- `x = [1,1]` and dividend 10 it holds; with `x = [-1,-1]` and dividend `min`
-- the division would overflow, so it is declined.
def divSafe (dividend : Expr) : BExp :=
  .not (.and (.cmp .eq dividend (.const I32.min))
             (.cmp .eq (.var "x") (.const (c (-1)))))

#guard D.entails (st 1 1 0 1) (divSafe (.const (c 10)))
#guard !D.entails (st (-1) (-1) 0 1) (divSafe (.const I32.min))

/-! ## `initOf` and `init_sound` -/

def p0 : Program := { body := .skip 0, arrays := #[] }

#guard (D.initOf p0).vars "x" = Interval.toInterval (c 0)
#guard (D.initOf p0).vars "i" = Interval.toInterval (c 0)
#guard (D.initOf p0).mem 0 = Interval.toInterval (c 0)

-- The checker's base case: if `P` holds at `State.init p`, the domain's initial
-- abstract state describes it.
example (p : Program) (hP : D.P (State.init p)) :
    D.gamma (D.initOf p) (State.init p) :=
  D.init_sound p hP

-- The canonical `lengths` is the program's array table; then `POn` holds at the
-- initial state, so `init_sound` discharges the base case with no extra premise.
example (p : Program) :
    GammaOn (fun a => p.arrays.getD a 0) ["x"] [] (initOf ["x"] [] p) (State.init p) :=
  initOf_sound p (POn_init p)

-- The entry obligation will be `ble (initOf p) (I entry)`; `top` is a valid
-- entry box, and `ble` is the field the checker calls.
#guard D.ble (D.initOf p0) D.top

/-! ## `P_step`: the induction invariant -/

-- The checker gets `P s` at a reachable state and must carry it to `s'`.
example (c : EdgeCmd) (s s' : State) (hP : D.P s)
    (h : EdgeCmd.exec c s = some s') : D.P s' :=
  D.P_step hP h

-- A concrete store preserves the array length, which is what `POn` tracks.
def s0 : State :=
  { env := fun _ => I32.zero,
    mem := fun a => if a = 0 then #[c 0, c 0] else #[] }

example : POn lengths s0 := by
  intro a
  by_cases ha : a = 0 <;> simp [s0, State.memAt, lengths, ha]

example (h : EdgeCmd.exec (.atomic (.store 0 (.const (c 0)) (.const (c 5)))) s0
    = some (s0.setMem 0 ((s0.memAt 0).set 0 (c 5)))) :
    POn lengths (s0.setMem 0 ((s0.memAt 0).set 0 (c 5))) :=
  POn_step (lengths := lengths) (by
    intro a
    by_cases ha : a = 0 <;> simp [s0, State.memAt, lengths, ha]) h

/-! ## `entails_sound`: the contract the checker relies on -/

example (a : Interval.Abs) (b : BExp) (s : State)
    (h : D.entails a b = true) (hP : D.P s) (hg : D.gamma a s) :
    evalB b s = some true :=
  D.entails_sound h hP hg
