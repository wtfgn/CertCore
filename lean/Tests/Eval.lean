import CertCore.Semantics

/-!
# `eval` / `evalB` smoke tests

Build-time checks of the M1.5 evaluation layer. Run with:

    lake env lean lean/Tests/Eval.lean

These pin the four failure modes (`/0`, `min / -1`, signed overflow,
out-of-bounds read) and the two semantic choices M1.5 had to make: division
truncates toward zero (not Lean's Euclidean division), and `and`/`or` are strict
(both sides evaluated, so a failing right operand still fails). Every
expectation is a `#guard`, so a wrong one fails the build.
-/

open CertCore

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-- One array of length 3. -/
def sample : Program := { body := .skip 0, arrays := #[3] }

/-- State with all variables zero and the array zero-filled. -/
def st : State := State.init sample

-- Atoms and arithmetic.
#guard eval (.const (c 5)) st = some (c 5)
#guard eval (.var "x") st = some I32.zero
#guard eval (.add (.var "x") (.const (c 3))) st = some (c 3)

-- Signed overflow is a failure.
#guard eval (.add (.const (c 2147483647)) (.const (c 1))) st = none
#guard eval (.sub (.const (c (-2147483648))) (.const (c 1))) st = none
#guard eval (.mul (.const (c 46341)) (.const (c 46341))) st = none

-- Division: truncation toward zero, zero divisor, and the single overflow case.
#guard eval (.div (.const (c 10)) (.const (c 0))) st = none
#guard eval (.div (.const (c (-7))) (.const (c 2))) st = some (c (-3))
#guard eval (.div (.const (c 7)) (.const (c (-2)))) st = some (c (-3))
#guard eval (.div (.const (c (-7))) (.const (c (-2)))) st = some (c 3)
#guard eval (.div (.const I32.min) (.const (c (-1)))) st = none

-- Array reads: in bounds return the cell, out of bounds fail.
#guard eval (.read 0 (.const (c 0))) st = some I32.zero
#guard eval (.read 0 (.const (c 2))) st = some I32.zero
#guard eval (.read 0 (.const (c 3))) st = none
#guard eval (.read 0 (.const (c (-1)))) st = none

-- Length comes from the state; an undeclared array number is empty.
#guard eval (.len 0) st = some (c 3)
#guard eval (.len 9) st = some I32.zero

-- Conditions.
#guard evalB (.cmp .lt (.const (c 1)) (.const (c 2))) st = some true
#guard evalB (.cmp .ge (.const (c 2)) (.const (c 2))) st = some true
#guard evalB (.not (.cmp .eq (.const (c 1)) (.const (c 2)))) st = some true
#guard evalB (.cmp .lt (.var "x") (.const (c 1))) (st.set "x" (c 0)) = some true

-- `and`/`or` are strict: a failing right operand is evaluated anyway.
#guard evalB (.and (.cmp .eq (.const (c 0)) (.const (c 0)))
                   (.cmp .eq (.div (.const (c 1)) (.const (c 0))) (.const (c 0)))) st = none
#guard evalB (.or (.cmp .eq (.const (c 0)) (.const (c 1)))
                  (.cmp .eq (.div (.const (c 1)) (.const (c 0))) (.const (c 0)))) st = none
