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

/-- Concrete states matching an abstract array state. The memory condition is
only required for in-bounds cells. -/
def AbsSound (lengths : Arr → Nat) (abs : Abs) (s : State) : Prop :=
  (∀ x, gamma (abs.vars x) (s.get x)) ∧
  (∀ a, (s.memAt a).size = lengths a) ∧
  (∀ (a : Arr) (i : Nat), i < (s.memAt a).size →
    gamma (abs.mem a) ((s.memAt a).getD i I32.zero))

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

/-- Expression transfer over `Abs`. Arithmetic delegates to M2.6; `read` returns
the array's interval and `len` returns the declared length when it fits. -/
def evalExprAbs (lengths : Arr → Nat) (abs : Abs) : Expr → Interval
  | .const n => toInterval n
  | .var x => abs.vars x
  | .add l r => add (evalExprAbs lengths abs l) (evalExprAbs lengths abs r)
  | .sub l r => sub (evalExprAbs lengths abs l) (evalExprAbs lengths abs r)
  | .mul _ _ => top
  | .div _ _ => top
  | .read a _ => abs.mem a
  | .len a => lenInterval lengths a

/-- Assignment updates the variable component; memory is unchanged. -/
def assignAbs (lengths : Arr → Nat) (abs : Abs) (x : Var) (e : Expr) : Abs :=
  { abs with vars := funUpdate abs.vars x (evalExprAbs lengths abs e) }

/-- **T4c (arrays):** `evalExprAbs` is sound for successful evaluation. -/
theorem evalExprAbs_sound {lengths : Arr → Nat} {abs : Abs} {s : State}
    {e : Expr} {v : I32} (hs : AbsSound lengths abs s)
    (h : eval e s = some v) : gamma (evalExprAbs lengths abs e) v := by
  induction e generalizing v with
  | const n =>
      simp only [eval] at h
      cases h
      simp [evalExprAbs]
  | var x =>
      simp only [eval] at h
      cases h
      simpa [evalExprAbs] using hs.1 x
  | add l r ihl ihr =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨v1, h1, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨v2, h2l, h2r⟩
      exact add_sound (ihl h1) (ihr h2l) h2r
  | sub l r ihl ihr =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨v1, h1, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨v2, h2l, h2r⟩
      exact sub_sound (ihl h1) (ihr h2l) h2r
  | mul l r ihl ihr =>
      simp [evalExprAbs]
  | div l r ihl ihr =>
      simp [evalExprAbs]
  | read a i ihi =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨idx, hidx, hrest⟩
      split at hrest
      · rename_i hcond
        cases hrest
        have hnonneg : 0 ≤ idx.val := hcond.1
        have hlt : idx.val.toNat < (s.memAt a).size := by
          have hcast : (idx.val.toNat : Int) = idx.val := Int.toNat_of_nonneg hnonneg
          omega
        simpa [evalExprAbs] using hs.2.2 a idx.val.toNat hlt
      · simp at hrest
  | len a =>
      simp only [eval] at h
      have hlen : (s.memAt a).size = lengths a := hs.2.1 a
      rw [hlen] at h
      cases hof : I32.ofInt? (lengths a : Int) with
      | none => simp [hof] at h
      | some n =>
          have hn : n = v := by
            simpa [hof] using h
          subst n
          simp [evalExprAbs, lenInterval, hof]

/-- **T4c (array assignment):** assigning an expression keeps `AbsSound`. -/
theorem assignAbs_sound {lengths : Arr → Nat} {abs : Abs} {s : State}
    {x : Var} {e : Expr} {v : I32} (hs : AbsSound lengths abs s)
    (h : eval e s = some v) :
    AbsSound lengths (assignAbs lengths abs x e) (s.set x v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = x
    · subst y
      have he := evalExprAbs_sound hs h
      simpa [assignAbs, State.set, State.get, funUpdate] using he
    · simpa [assignAbs, State.set, State.get, funUpdate, hy] using hs.1 y
  · intro a
    simpa [State.set, State.memAt] using hs.2.1 a
  · intro a i hi
    simpa [assignAbs, State.set, State.memAt] using hs.2.2 a i hi

end Interval
end CertCore
