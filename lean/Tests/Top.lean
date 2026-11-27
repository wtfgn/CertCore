import CertCore.Domain.Interval

/-!
# `top` smoke tests (M2.5)

Run with:

    lake env lean lean/Tests/Top.lean

Pins the no-information element: every value is in `top`, every interval is
included in it, and it absorbs in `join`.
-/

open CertCore

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

-- Every value is in top.
example (v : I32) : Interval.gamma Interval.top v := Interval.top_sound v

-- Every interval is included in top.
#guard Interval.ble (between 0 5) Interval.top
#guard Interval.ble .bot Interval.top
#guard Interval.ble (Interval.ofBounds none (some (c 10))) Interval.top

-- Top absorbs in join.
#guard Interval.join (between 0 5) Interval.top = Interval.top
#guard Interval.join Interval.top (between 0 5) = Interval.top
#guard Interval.join .bot Interval.top = Interval.top

-- Top is `(none, none)`.
#guard Interval.top = .itv none none (by trivial)
