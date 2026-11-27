import CertCore.Domain.IntervalTransfer

/-!
# `CertCore.Domain.IntervalArrays` — array read/len and bounds (M2.7)

The abstract state has one interval per variable and one interval per array. The
array interval over-approximates **every cell** of that array; a read therefore
returns the whole array interval. Array lengths come from the declared
`Program.arrays` and are supplied as `lengths : Arr → Nat`.

`idxWithin idx len` is the safety predicate the checker will use for array
access: the abstract index must be non-negative and strictly below `len`.
-/

namespace CertCore
namespace Interval

/-- Abstract interval state: variable intervals plus one interval per array. -/
structure Abs where
  /-- Variable intervals. -/
  vars : Var → Interval
  /-- One interval covering every cell of each array. -/
  mem : Arr → Interval

/-- The abstract interval for `len a`, or `top` when the declared length does not
fit in `I32` (in which case concrete `len` cannot succeed either). -/
def lenInterval (lengths : Arr → Nat) (a : Arr) : Interval :=
  match I32.ofInt? (lengths a : Int) with
  | some n => toInterval n
  | none => top

/-- The bounds safety predicate for an array access: every value in the abstract
index interval is in `[0, len)`. An empty index interval is vacuously safe. -/
def idxWithin : Interval → Nat → Bool
  | .bot, _ => true
  | .itv lo hi _, len =>
      (match lo with
       | none => false
       | some a => decide (0 ≤ a.val)) &&
      (match hi with
       | none => false
       | some b => decide (b.val < (len : Int)))

/-- **Bounds obligation (T4-style):** `idxWithin` implies every concrete index in
the interval is within `[0, len)`. -/
theorem idxWithin_sound {idx : Interval} {len : Nat} {i : I32}
    (h : idxWithin idx len = true) (hi : gamma idx i) :
    0 ≤ i.val ∧ i.val < (len : Int) := by
  cases idx with
  | bot => simp [gamma] at hi
  | itv lo hiu w =>
      simp only [idxWithin, Bool.and_eq_true] at h
      have hg : lowerOk lo i ∧ upperOk hiu i := by simpa [gamma] using hi
      cases lo with
      | none => simp at h
      | some a =>
          cases hiu with
          | none => simp at h
          | some b =>
              have h0 : 0 ≤ a.val := of_decide_eq_true h.1
              have hlt : b.val < (len : Int) := of_decide_eq_true h.2
              have ha : a.val ≤ i.val := (lowerOk_some a i).1 hg.1
              have hb : i.val ≤ b.val := (upperOk_some b i).1 hg.2
              exact ⟨by omega, by omega⟩

/-! The expression/assignment transfer over `Abs` lives in `IntervalInstance`
(`evalExprAbsOn`/`assignAbsOn`, with `GammaOn`), which is the single transfer on
the final path. This module keeps the abstract state and the array-specific
operations (`lenInterval`, `idxWithin`). -/

end Interval
end CertCore
