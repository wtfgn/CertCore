import CertCore.Domain.Interval

/-!
# `join` and `join_sound` smoke tests (M2.4)

Run with:

    lake env lean lean/Tests/Join.lean

Pins the convex hull: `bot` is the identity, finite intervals widen to the
minimum lower / maximum upper bound, unbounded sides absorb, and `join_sound`
puts both operands inside the hull.
-/

open CertCore

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

def top : Interval := .itv none none (by trivial)
def singleton (n : Int) : Interval := Interval.toInterval (c n)

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

/-! ## Shape of the hull -/

#guard Interval.join .bot (between 0 5) = between 0 5
#guard Interval.join (between 0 5) .bot = between 0 5
#guard Interval.join (between 0 1) (between 3 4) = between 0 4
#guard Interval.join (between 0 5) (between 2 10) = between 0 10
#guard Interval.join (between 0 5) (between 0 5) = between 0 5

/-! ## Unbounded sides and top -/

#guard Interval.join (between 0 5) (Interval.ofBounds none (some (c 10))) =
  Interval.ofBounds none (some (c 10))
#guard Interval.join (Interval.ofBounds none (some (c 0)))
    (Interval.ofBounds (some (c 5)) none) = top
#guard Interval.join (between 0 5) top = top
#guard Interval.join top (between 0 5) = top

/-! ## `join_sound` -/

example : Interval.gamma (Interval.join (singleton 0) (singleton 5)) (c 0) :=
  Interval.join_sound (a := singleton 0) (b := singleton 5) (v := c 0)
    (Or.inl (Interval.gamma_toInterval (c 0)))

example : Interval.gamma (Interval.join (singleton 0) (singleton 5)) (c 5) :=
  Interval.join_sound (a := singleton 0) (b := singleton 5) (v := c 5)
    (Or.inr (Interval.gamma_toInterval (c 5)))

example : Interval.gamma (Interval.join .bot top) (c 42) :=
  Interval.join_sound (a := .bot) (b := top) (v := c 42)
    (Or.inr (by
      simp [Interval.gamma, top, Interval.lowerOk, Interval.upperOk]))
