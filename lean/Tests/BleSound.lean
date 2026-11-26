import CertCore.Domain.Interval

/-!
# `ble_sound` smoke tests (M2.4)

Run with:

    lake env lean lean/Tests/BleSound.lean

Exercises the inclusion theorem on concrete inclusions and on `bot`/`top`.
-/

open CertCore

def c (n : Int) : I32 := I32.ofIntWrap n

def top : Interval := .itv none none (by trivial)

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

example : ∀ v, Interval.gamma (between 0 5) v → Interval.gamma (between 0 10) v :=
  Interval.ble_sound (by decide)

example : ∀ v, Interval.gamma .bot v → Interval.gamma (between 0 10) v :=
  Interval.ble_sound (by decide)

example : ∀ v, Interval.gamma (between 0 5) v → Interval.gamma top v :=
  Interval.ble_sound (by decide)

example : ∀ v, Interval.gamma (Interval.toInterval (c 5)) v →
    Interval.gamma (between 0 10) v :=
  Interval.ble_sound (by decide)

example : ∀ v, Interval.gamma (Interval.ofBounds none (some (c 10))) v →
    Interval.gamma top v :=
  Interval.ble_sound (by decide)
