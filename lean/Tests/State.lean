import CertCore.Semantics

/-!
# `State` smoke tests

Build-time checks of the M1.4 state layer. Run with:

    lake env lean lean/Tests/State.lean

Pins the properties the semantics will rely on: the environment and memory are
total, variables start at zero, `set`/`get` interact pointwise, arrays are
allocated at their declared lengths, and an array number outside `Program.arrays`
reads as the empty array instead of getting stuck. Every expectation is a
`#guard`, so a wrong one fails the build.
-/

open CertCore

/-- In-range test constant. -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-- Three arrays: lengths 3, 0, 2. -/
def sample : Program := { body := .skip 0, arrays := #[3, 0, 2] }

-- The environment is total and zero-initialised.
#guard (State.init sample).get "x" = I32.zero
#guard (State.init sample).get "never-declared" = I32.zero

-- `set` then `get`: same variable is updated, others are untouched.
#guard ((State.init sample).set "x" (c 7)).get "x" = c 7
#guard ((State.init sample).set "x" (c 7)).get "y" = I32.zero

-- Arrays have their declared lengths and are zero-filled.
#guard ((State.init sample).memAt 0).size = 3
#guard ((State.init sample).memAt 1).size = 0
#guard ((State.init sample).memAt 2).size = 2
#guard ((State.init sample).memAt 0).getD 2 I32.zero = I32.zero

-- An out-of-range array number is the empty array, not a stuck state.
#guard ((State.init sample).memAt 9).size = 0

-- Whole-array replacement is visible and leaves other arrays alone.
#guard ((State.init sample).setMem 0 #[c 4, c 5, c 6]).memAt 0 = #[c 4, c 5, c 6]
#guard ((State.init sample).setMem 0 #[c 4, c 5, c 6]).memAt 2 = (State.init sample).memAt 2
