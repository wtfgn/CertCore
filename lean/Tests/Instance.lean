import CertCore.Domain.IntervalInstance

/-!
# Interval `CertDomain` smoke tests (M2.8)

Run with:

    lake env lean lean/Tests/Instance.lean

Pins the assembled instance: `ble`, `top`, `join`, `transfer` for assign and
store, and the `POn`/`GammaOn` shape.
-/

open CertCore

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

def lengths : Arr → Nat := fun a => if a = 0 then 2 else 0

def D : CertDomain := Interval.intervalDomain lengths ["x"] [0]

def abs : Interval.Abs :=
  { vars := fun v => if v = "x" then Interval.toInterval (c 1) else Interval.top,
    mem := fun a => if a = 0 then between 10 20 else Interval.top }

#guard D.ble abs Interval.topAbs
#guard !D.ble Interval.topAbs abs
#guard D.ble Interval.topAbs Interval.topAbs

#guard (D.transfer (.atomic (.assign "x" (.const (c 5)))) abs).vars "x" =
  Interval.toInterval (c 5)
#guard (D.transfer (.atomic (.store 0 (.const (c 0)) (.const (c 5)))) abs).mem 0 =
  Interval.top

#guard (D.join abs abs).vars "x" = Interval.toInterval (c 1)
#guard (D.join abs Interval.topAbs).vars "x" = Interval.top
#guard (D.join abs abs).mem 0 = between 10 20

def st0 : State :=
  { env := fun _ => I32.zero,
    mem := fun a => if a = 0 then #[c 0, c 0] else #[] }

example : D.gamma D.top st0 := by
  apply Interval.topAbs_sound
  intro a
  by_cases ha : a = 0 <;> simp [st0, State.memAt, lengths, ha]
