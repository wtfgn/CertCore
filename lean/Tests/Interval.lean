import CertCore.Domain.Interval

/-!
# `Interval` smoke tests (M2.1)

Run with:

    lake env lean lean/Tests/Interval.lean

Pins the canonical constructors: `toInterval` is a singleton; `ofBounds?`
rejects inverted bounds while `ofBounds` normalises them to `bot`; unbounded
sides are `none`; and the empty/non-empty distinction is decidable.
-/

open CertCore

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

#guard Interval.toInterval (c 5) = .itv (some (c 5)) (some (c 5)) (by decide)
#guard Interval.toInterval (c 0) ≠ .bot

-- The checked constructor rejects inverted bounds; the normalising one maps them
-- to `bot` for internal use.
#guard Interval.ofBounds? (some (c 5)) (some (c 3)) = none
#guard Interval.ofBounds? (some (c 3)) (some (c 5)) =
  some (.itv (some (c 3)) (some (c 5)) (by decide))
#guard Interval.ofBounds? none none = some (.itv none none (by trivial))
#guard Interval.ofBounds (some (c 5)) (some (c 3)) = .bot

-- Inverted finite bounds are the empty interval after normalisation.
#guard Interval.ofBounds (some (c 5)) (some (c 3)) = .bot

-- Ordered finite bounds build the interval.
#guard Interval.ofBounds (some (c 3)) (some (c 5)) =
  .itv (some (c 3)) (some (c 5)) (by decide)

-- Unbounded sides are `none`; `(none, none)` is top.
#guard Interval.ofBounds none none = .itv none none (by trivial)
#guard Interval.ofBounds none (some (c 5)) = .itv none (some (c 5)) (by trivial)
#guard Interval.ofBounds (some (c 5)) none = .itv (some (c 5)) none (by trivial)

-- Equality is decidable and distinguishes the empty case.
#guard (Interval.toInterval (c 5) == Interval.toInterval (c 5))
#guard (Interval.toInterval (c 5) != Interval.bot)

example : Interval.toInterval (c 5) ≠ .bot := by
  intro h
  cases h
