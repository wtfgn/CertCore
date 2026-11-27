import CertCore.Domain.Interval

/-!
# `ble` smoke tests (M2.3)

Run with:

    lake env lean lean/Tests/Ble.lean

Pins the inclusion decision: `bot` is included in everything, no non-empty
interval is included in `bot`, the endpoint effects of `none` are asymmetric,
and `top` contains every interval.
-/

open CertCore

/-- In-range test value. -/
def c (n : Int) : I32 := I32.ofIntWrap n

def top : Interval := .itv none none (by trivial)
def singleton (n : Int) : Interval := Interval.toInterval (c n)

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

/-! ## `bot` -/

#guard Interval.ble .bot .bot
#guard Interval.ble .bot (singleton 0)
#guard !Interval.ble (singleton 0) .bot

/-! ## Finite intervals -/

#guard Interval.ble (singleton 5) (between 0 10)
#guard !Interval.ble (between 0 10) (singleton 5)
#guard !Interval.ble (singleton 5) (singleton 4)
#guard Interval.ble (between 0 5) (between 0 5)
#guard Interval.ble (between 1 4) (between 0 5)
#guard !Interval.ble (between 0 5) (between 1 4)

/-! ## Unbounded sides -/

#guard Interval.ble (between 0 5) (Interval.ofBounds none (some (c 10)))
#guard !Interval.ble (Interval.ofBounds none (some (c 10))) (between 0 5)
#guard Interval.ble (between 0 5) (Interval.ofBounds (some (c 0)) none)
#guard !Interval.ble (Interval.ofBounds (some (c 0)) none) (between 0 5)
#guard Interval.ble (Interval.ofBounds none none) (Interval.ofBounds none none)
#guard !Interval.ble (Interval.ofBounds none none) (Interval.ofBounds (some (c 0)) none)

/-! ## Top -/

#guard Interval.ble (singleton 5) top
#guard Interval.ble .bot top
#guard !Interval.ble top (singleton 5)
#guard !Interval.ble top (Interval.ofBounds none (some (c 10)))

/-! ## Endpoint orders -/

#guard Interval.leLo none (some (c 0))
#guard !Interval.leLo (some (c 0)) none
#guard Interval.leLo (some I32.min) none
#guard Interval.leLo (some (c 1)) (some (c 2))
#guard !Interval.leLo (some (c 2)) (some (c 1))

#guard Interval.leHi (some (c 1)) (some (c 2))
#guard !Interval.leHi none (some (c 10))
#guard Interval.leHi none (some I32.max)
#guard Interval.leHi (some (c 1)) none
#guard Interval.leHi none none

/-! ## `ble_complete` (F4)

The completeness half of T4: semantic inclusion implies the executable test. -/

example {a b : Interval} (h : ∀ v, Interval.gamma a v → Interval.gamma b v) :
    Interval.ble a b = true :=
  Interval.ble_complete h

-- The `i32Min`/`i32Max` edge cases are exactly what completeness needs.
example : Interval.ble (Interval.ofBounds none (some (c 10)))
    (Interval.ofBounds none (some I32.max)) := by
  apply Interval.ble_complete
  intro v hv
  refine ⟨Interval.lowerOk_none v, ?_⟩
  exact (Interval.upperOk_some I32.max v).2 (by
    have hmax : I32.max.val = i32Max := rfl
    rw [hmax]
    exact v.le_max)
