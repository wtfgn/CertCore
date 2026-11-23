import CertCore.I32

/-!
# `I32` smoke tests

Build-time checks of the M1.1 boundary cases. Run with:

    lake env lean lean/Tests/I32.lean

Every arithmetic expectation below is a `#guard`: if it is false, elaborating this
file fails, and CI fails with it. `#guard` is a test, not a theorem — it elaborates
the expression at type `Bool` (a `Prop` is coerced through `decide`), evaluates it
with Lean's unsafe evaluator, and reports an error when the result is not `true`.
It adds no declaration and no proof term, so it belongs to the same trust class as
`#eval`. The difference that matters is that `#eval` only prints: a stale value
would pass unnoticed, whereas `#guard` turns the expectation into a build failure.

This file is deliberately outside the library target — `lake build` does not run
it. CI runs it explicitly, and the README lists the command.

The final section keeps four representative printed forms under `#guard_msgs`, so
`Repr`/`ToString` output is checked without restating every case.
-/

open CertCore

/-- Build a test value through the machine conversion (exact for in-range inputs). -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-! ## Range endpoints are representable. -/

#guard (c 2147483647).val = 2147483647
#guard (c (-2147483648)).val = -2147483648

/-! ## Checked addition: overflow is refused, the last in-range result is accepted. -/

#guard I32.add? (c 2147483647) (c 1) = none
#guard I32.add? (c 2147483646) (c 1) = some (c 2147483647)

/-! ## The machine wraps the same addition to the minimum value. -/

#guard (I32.addWrap (c 2147483647) (c 1)).val = -2147483648

/-! ## Checked subtraction: min - 1 overflows; the machine wraps to max. -/

#guard I32.sub? (c (-2147483648)) (c 1) = none
#guard (I32.subWrap (c (-2147483648)) (c 1)).val = 2147483647

/-! ## Multiplication around the square-root boundary of 2^31. -/

#guard I32.mul? (c 46340) (c 46340) = some (c 2147395600)
#guard I32.mul? (c 46341) (c 46341) = none

/-! ## Negation overflows only at min. -/

#guard I32.neg? (c (-2147483648)) = none
#guard I32.neg? (c 5) = some (c (-5))

/-! ## Division truncates toward zero and fails on zero and on `min / -1`. -/

#guard I32.div? (c (-7)) (c 2) = some (c (-3))
#guard I32.div? (c 7) (c (-2)) = some (c (-3))
#guard I32.div? (c (-7)) (c (-2)) = some (c 3)
#guard I32.div? (c 1) (c 0) = none
#guard I32.div? (c (-2147483648)) (c (-1)) = none

/-! ## Wrap conversions for values two words wide and just below min. -/

#guard (I32.ofIntWrap 4294967296).val = 0
#guard (I32.ofIntWrap (-2147483649)).val = 2147483647

/-! ## An out-of-range source literal must be refused. -/

#guard I32.ofInt? 2147483648 = none
#guard I32.ofInt? 2147483647 = some (c 2147483647)

/-! ## Representative printed forms (`Repr` / `ToString`). -/

/-- info: none -/
#guard_msgs in
#eval I32.add? (c 2147483647) (c 1)

/-- info: some 2147395600 -/
#guard_msgs in
#eval I32.mul? (c 46340) (c 46340)

/-- info: -2147483648 -/
#guard_msgs in
#eval (I32.addWrap (c 2147483647) (c 1)).val

/-- info: some -5 -/
#guard_msgs in
#eval I32.neg? (c 5)
