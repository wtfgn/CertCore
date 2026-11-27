import CertCore.Domain.IntervalInstance

/-!
# Array transfer smoke tests (M2.7/F6)

Run with:

    lake env lean lean/Tests/Arrays.lean

The final array evaluator is `evalExprAbsOn` with `GammaOn` (the M2.7
`AbsSound` evaluator was removed at F6). This file pins per-array interval
reads, `len` from the declared lengths, the `idxWithin` bounds predicate and its
soundness, and T4c for read/len.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def between (lo hi : Int) : Interval :=
  Interval.ofBounds (some (c lo)) (some (c hi))

theorem cval (n : Int) (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    (c n).val = n :=
  I32.ofIntWrap_val_of_bounds (by simpa [i32Min] using h1)
    (by simpa [i32Max] using h2)

theorem mem_0_9_5 : Interval.gamma (between 0 9) (c 5) := by
  have h0 : (c 0).val = 0 := cval 0 (by omega) (by omega)
  have h5 : (c 5).val = 5 := cval 5 (by omega) (by omega)
  have h9 : (c 9).val = 9 := cval 9 (by omega) (by omega)
  have hc : (c 0).val ≤ (c 9).val := by omega
  rw [between, Interval.ofBounds_of_le hc]
  rw [Interval.gamma_itv]
  simp only [Interval.lowerOk_some, Interval.upperOk_some]
  constructor <;> omega

def lengths2 : Arr → Nat := fun a => if a = 0 then 2 else 0

def abs : Interval.Abs :=
  { vars := fun _ => Interval.top,
    mem := fun a => if a = 0 then between 10 20 else Interval.top }

/-! ## Read and len -/

#guard evalExprAbsOn lengths2 [] [0] abs (.read 0 (.const (c 0))) = between 10 20
#guard evalExprAbsOn lengths2 [] [0] abs (.len 0) = Interval.toInterval (c 2)

-- A declared length that does not fit in I32 collapses `len` to top.
#guard evalExprAbsOn (fun _ => 4294967296) [] [0] abs (.len 0) = Interval.top

/-! ## `idxWithin` -/

#guard Interval.idxWithin (between 0 9) 10
#guard !Interval.idxWithin (between 0 10) 10
#guard !Interval.idxWithin (between (-1) 9) 10
#guard !Interval.idxWithin (Interval.ofBounds none (some (c 9))) 10
#guard !Interval.idxWithin (Interval.ofBounds (some (c 0)) none) 10
#guard Interval.idxWithin Interval.bot 0

example : 0 ≤ (c 5).val ∧ (c 5).val < (10 : Int) :=
  Interval.idxWithin_sound (len := 10) (by decide) mem_0_9_5

/-! ## T4c for read and len -/

def st : State :=
  { env := fun _ => I32.zero,
    mem := fun a => if a = 0 then #[c 10, c 20] else #[] }

theorem mem_10_20 (n : Int) (h1 : 10 ≤ n) (h2 : n ≤ 20) :
    Interval.gamma (between 10 20) (c n) := by
  have h10 : (c 10).val = 10 := cval 10 (by omega) (by omega)
  have h20 : (c 20).val = 20 := cval 20 (by omega) (by omega)
  have hc : (c 10).val ≤ (c 20).val := by omega
  have hn : (c n).val = n := cval n (by omega) (by omega)
  rw [between, Interval.ofBounds_of_le hc]
  rw [Interval.gamma_itv]
  simp only [Interval.lowerOk_some, Interval.upperOk_some]
  constructor <;> omega

theorem gammaOn : GammaOn lengths2 [] [0] abs st := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp at hx
  · intro a ha
    simp at ha
    subst a
    simp [st, lengths2, State.memAt]
  · intro a ha i hi
    simp at ha
    subst a
    have hi2 : i < 2 := by simpa [st, State.memAt] using hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · simpa [abs, st, State.memAt] using mem_10_20 10 (by omega) (by omega)
    · simpa [abs, st, State.memAt] using mem_10_20 20 (by omega) (by omega)

#guard eval (.read 0 (.const (c 0))) st = some (c 10)
#guard eval (.len 0) st = some (c 2)

example : Interval.gamma
    (evalExprAbsOn lengths2 [] [0] abs (.read 0 (.const (c 0)))) (c 10) := by
  apply evalExprAbsOn_sound (abs := abs) (s := st)
    (e := .read 0 (.const (c 0))) (v := c 10) gammaOn
  decide

example : Interval.gamma (evalExprAbsOn lengths2 [] [0] abs (.len 0)) (c 2) := by
  apply evalExprAbsOn_sound (abs := abs) (s := st) (e := .len 0) (v := c 2) gammaOn
  decide
