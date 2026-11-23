/-!
# `CertCore.I32` — signed 32-bit machine integers

`I32` is the value type the `Imp` semantics runs on (M1). It is an `Int` with a
proof that it lies in `[-2^31, 2^31 - 1]`.

Two layers, deliberately kept separate:

* **Checked arithmetic** (`add?`, `sub?`, `mul?`, `neg?`) returns `none` exactly
  when the mathematical result does not fit. `eval` (M1.5) turns that `none` into
  a stuck state, so **signed overflow is an observable safety violation** — not a
  silent wrap, and not an impossibility by construction (roadmap M1.1).
* **Wrap arithmetic** (`addWrap`, …) is the machine behaviour: the mathematical
  result reduced modulo `2^32` into the signed range. `*?_wrap` proves the two
  agree whenever the checked operation succeeds, so the model of the machine and
  the model of the error cannot drift apart.

Division and remainder are defined with `eval` in M1.5: their failure modes
(dividing by zero, and `min / -1` overflow) are semantic, and their rounding
convention belongs with the expression semantics.

No Mathlib. The representation is `Int`-backed rather than a `UInt32` because
every later proof (interval transfer, safety predicates) reasons about ranges;
`Int` keeps those proofs short, and the checker's hot path is interval inclusion,
not integer construction.
-/

namespace CertCore

/-- Smallest signed 32-bit integer, `-2^31`. -/
def i32Min : Int := -2147483648

/-- Largest signed 32-bit integer, `2^31 - 1`. -/
def i32Max : Int := 2147483647

/-- A signed 32-bit machine integer: an `Int` with a range proof.

The proof fields are what make overflow a property of operations rather than of
the type: a value can never be out of range, so a computation that would leave
the range must be reported. -/
structure I32 where
  val : Int
  min_le : i32Min ≤ val
  le_max : val ≤ i32Max

namespace I32

/-- Two `I32`s are equal when their values are. -/
@[ext] theorem ext {a b : I32} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

instance : DecidableEq I32 := fun a b =>
  if h : a.val = b.val then isTrue (ext h)
  else isFalse (fun hab => h (congrArg I32.val hab))

instance : Repr I32 := ⟨fun a _ => repr a.val⟩

instance : ToString I32 := ⟨fun a => toString a.val⟩

instance : Coe I32 Int := ⟨I32.val⟩

/-- The mathematical value of a machine integer. -/
def toInt (a : I32) : Int := a.val

@[simp] theorem toInt_mk (n : Int) (h1 : i32Min ≤ n) (h2 : n ≤ i32Max) :
    toInt ⟨n, h1, h2⟩ = n := rfl

/-- Convert an integer to `I32`, failing when it is out of range. This is the
constructor used for source literals and for safety checks. -/
def ofInt? (n : Int) : Option I32 :=
  if h : i32Min ≤ n ∧ n ≤ i32Max then some ⟨n, h.1, h.2⟩ else none

/-- The machine conversion: reduce arbitrary integers modulo `2^32` into the
signed range. Total, and used only to model wrap-around, never to hide an
overflow. -/
def ofIntWrap (n : Int) : I32 :=
  let m := (n + 2147483648) % 4294967296
  ⟨m - 2147483648,
    (by have hm : 0 ≤ m := Int.emod_nonneg _ (by decide); simp only [i32Min]; omega),
    (by have hm : m < 4294967296 := Int.emod_lt_of_pos _ (by decide); simp only [i32Max]; omega)⟩

/-- The smallest representable value. -/
def min : I32 := ⟨i32Min, by decide, by decide⟩

/-- The largest representable value. -/
def max : I32 := ⟨i32Max, by decide, by decide⟩

/-- Zero. -/
def zero : I32 := ⟨0, by decide, by decide⟩

/-- One. -/
def one : I32 := ⟨1, by decide, by decide⟩

instance : Inhabited I32 := ⟨zero⟩

/-- Numerals are machine literals: out-of-range numerals wrap, exactly like a
C programmer's `0x100000000`. Use `ofInt?` when the failure must be visible. -/
instance (n : Nat) : OfNat I32 n := ⟨ofIntWrap (Int.ofNat n)⟩

/-! ## Checked arithmetic -/

/-- Addition, failing on signed overflow. -/
def add? (a b : I32) : Option I32 := ofInt? (a.val + b.val)

/-- Subtraction, failing on signed overflow. -/
def sub? (a b : I32) : Option I32 := ofInt? (a.val - b.val)

/-- Multiplication, failing on signed overflow. -/
def mul? (a b : I32) : Option I32 := ofInt? (a.val * b.val)

/-- Negation, failing on the one overflow case (`-min`). -/
def neg? (a : I32) : Option I32 := ofInt? (-a.val)

/-! ## Wrap-around (the machine model) -/

/-- Wrapping addition. -/
def addWrap (a b : I32) : I32 := ofIntWrap (a.val + b.val)

/-- Wrapping subtraction. -/
def subWrap (a b : I32) : I32 := ofIntWrap (a.val - b.val)

/-- Wrapping multiplication. -/
def mulWrap (a b : I32) : I32 := ofIntWrap (a.val * b.val)

/-- Wrapping negation. -/
def negWrap (a : I32) : I32 := ofIntWrap (-a.val)

/-! ## Lemmas about the conversions -/

theorem ofInt?_sound {n : Int} {a : I32} (h : ofInt? n = some a) : a.val = n := by
  unfold ofInt? at h
  split at h
  · rename_i hn
    injection h with hc
    rw [← hc]
  · contradiction

theorem ofInt?_complete {n : Int} (h1 : i32Min ≤ n) (h2 : n ≤ i32Max) :
    ofInt? n = some ⟨n, h1, h2⟩ := by
  unfold ofInt?
  split
  · rename_i hn
    congr 1
  · rename_i hn
    exact absurd ⟨h1, h2⟩ hn

theorem ofInt?_isSome_iff {n : Int} :
    (ofInt? n).isSome ↔ i32Min ≤ n ∧ n ≤ i32Max := by
  unfold ofInt?
  split
  · rename_i hn
    simp [hn]
  · rename_i hn
    simp [hn]

theorem ofInt?_none_iff {n : Int} :
    ofInt? n = none ↔ ¬(i32Min ≤ n ∧ n ≤ i32Max) := by
  unfold ofInt?
  split
  · rename_i hn
    simp [hn]
  · rename_i hn
    simp [hn]

/-- On in-range inputs the wrap conversion is the identity. -/
theorem ofIntWrap_val_of_bounds {n : Int} (h1 : i32Min ≤ n) (h2 : n ≤ i32Max) :
    (ofIntWrap n).val = n := by
  unfold ofIntWrap
  dsimp only
  simp only [i32Min, i32Max] at h1 h2
  have hm : (n + 2147483648) % 4294967296 = n + 2147483648 := by
    apply Int.emod_eq_of_lt <;> omega
  rw [hm]
  omega

/-- **Checked and wrap agree.** When the checked operation succeeds, the machine
wrap computes the same value: the error model is a refinement of the machine,
not a different machine. -/
theorem ofIntWrap_agrees {n : Int} {c : I32} (h : ofInt? n = some c) :
    (ofIntWrap n).val = c.val := by
  have hs : (ofInt? n).isSome := by rw [h]; rfl
  have hb := ofInt?_isSome_iff.mp hs
  rw [ofIntWrap_val_of_bounds hb.1 hb.2, ofInt?_sound h]

/-! ## Lemmas about the operations -/

theorem add?_sound {a b c : I32} (h : add? a b = some c) : c.val = a.val + b.val :=
  ofInt?_sound h

theorem add?_isSome_iff {a b : I32} :
    (add? a b).isSome ↔ i32Min ≤ a.val + b.val ∧ a.val + b.val ≤ i32Max :=
  ofInt?_isSome_iff (n := a.val + b.val)

theorem add?_none_iff {a b : I32} :
    add? a b = none ↔ ¬(i32Min ≤ a.val + b.val ∧ a.val + b.val ≤ i32Max) :=
  ofInt?_none_iff (n := a.val + b.val)

theorem add?_wrap {a b c : I32} (h : add? a b = some c) : (addWrap a b).val = c.val :=
  ofIntWrap_agrees h

theorem sub?_sound {a b c : I32} (h : sub? a b = some c) : c.val = a.val - b.val :=
  ofInt?_sound h

theorem sub?_isSome_iff {a b : I32} :
    (sub? a b).isSome ↔ i32Min ≤ a.val - b.val ∧ a.val - b.val ≤ i32Max :=
  ofInt?_isSome_iff (n := a.val - b.val)

theorem sub?_none_iff {a b : I32} :
    sub? a b = none ↔ ¬(i32Min ≤ a.val - b.val ∧ a.val - b.val ≤ i32Max) :=
  ofInt?_none_iff (n := a.val - b.val)

theorem sub?_wrap {a b c : I32} (h : sub? a b = some c) : (subWrap a b).val = c.val :=
  ofIntWrap_agrees h

theorem mul?_sound {a b c : I32} (h : mul? a b = some c) : c.val = a.val * b.val :=
  ofInt?_sound h

theorem mul?_isSome_iff {a b : I32} :
    (mul? a b).isSome ↔ i32Min ≤ a.val * b.val ∧ a.val * b.val ≤ i32Max :=
  ofInt?_isSome_iff (n := a.val * b.val)

theorem mul?_none_iff {a b : I32} :
    mul? a b = none ↔ ¬(i32Min ≤ a.val * b.val ∧ a.val * b.val ≤ i32Max) :=
  ofInt?_none_iff (n := a.val * b.val)

theorem mul?_wrap {a b c : I32} (h : mul? a b = some c) : (mulWrap a b).val = c.val :=
  ofIntWrap_agrees h

theorem neg?_sound {a c : I32} (h : neg? a = some c) : c.val = -a.val :=
  ofInt?_sound h

theorem neg?_isSome_iff {a : I32} :
    (neg? a).isSome ↔ i32Min ≤ -a.val ∧ -a.val ≤ i32Max :=
  ofInt?_isSome_iff (n := -a.val)

theorem neg?_none_iff {a : I32} :
    neg? a = none ↔ ¬(i32Min ≤ -a.val ∧ -a.val ≤ i32Max) :=
  ofInt?_none_iff (n := -a.val)

theorem neg?_wrap {a c : I32} (h : neg? a = some c) : (negWrap a).val = c.val :=
  ofIntWrap_agrees h

end I32
end CertCore
