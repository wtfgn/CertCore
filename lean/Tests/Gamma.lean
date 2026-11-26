import CertCore.Domain.Interval

/-!
# `gamma` smoke tests (M2.2)

Run with:

    lake env lean lean/Tests/Gamma.lean

Pins the membership predicate: `bot` is empty, `itv none none` is top, the
singleton contains exactly its point, and one-sided intervals respect their
finite side.
-/

open CertCore

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

-- `bot` is empty.
example : ¬ Interval.gamma .bot (c 0) := by
  simp [Interval.gamma]

-- `(none, none)` is top.
example : Interval.gamma (.itv none none (by trivial)) (c 0) := by
  simp [Interval.gamma, Interval.lowerOk, Interval.upperOk]

-- A singleton contains its point.
example : Interval.gamma (Interval.toInterval (c 5)) (c 5) :=
  Interval.gamma_toInterval (c 5)

-- ... and nothing else.
example : ¬ Interval.gamma (Interval.toInterval (c 5)) (c 4) := by
  intro h
  have h' : c 4 = c 5 := Interval.gamma_toInterval_iff.1 h
  exact absurd h' (by decide)

-- One-sided intervals use the finite side.
example : Interval.gamma (Interval.ofBounds none (some (c 5))) (c 5) := by
  simp [Interval.gamma, Interval.ofBounds, Interval.ofBounds?, Interval.lowerOk,
    Interval.upperOk]

example : ¬ Interval.gamma (Interval.ofBounds none (some (c 5))) (c 6) := by
  intro h
  simp [Interval.gamma, Interval.ofBounds, Interval.ofBounds?, Interval.lowerOk,
    Interval.upperOk] at h
  have h6 : (c 6).val = 6 := I32.ofIntWrap_val_of_bounds (by decide) (by decide)
  have h5 : (c 5).val = 5 := I32.ofIntWrap_val_of_bounds (by decide) (by decide)
  omega
