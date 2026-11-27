import CertCore.Domain
import CertCore.Domain.IntervalArrays

/-!
# `CertCore.Domain.IntervalInstance` — interval `CertDomain` (M2.8)

The instance is parameterised by the program's declared array lengths and by the
finite program support (`vars`, `arrays`). Concretisation `GammaOn` only
constrains the program support; expressions that mention an unknown variable or
array evaluate to `top`, so the instance is sound without a support proof on
`Abs`.

`POn` is the program state invariant: every array has its declared length.
-/

namespace CertCore
namespace Interval

/-- Concretisation over the program support. -/
def GammaOn (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr)
    (abs : Abs) (s : State) : Prop :=
  (∀ x, x ∈ vars → gamma (abs.vars x) (s.get x)) ∧
  (∀ a, a ∈ arrays → (s.memAt a).size = lengths a) ∧
  (∀ (a : Arr), a ∈ arrays → ∀ i, i < (s.memAt a).size →
    gamma (abs.mem a) ((s.memAt a).getD i I32.zero))

/-- Program state invariant: every array has its declared length. -/
def POn (lengths : Arr → Nat) (s : State) : Prop :=
  ∀ a, (s.memAt a).size = lengths a

/-- Computable array membership for the support-restricted evaluator. -/
def arrMem (a : Arr) (arrays : List Arr) : Bool :=
  arrays.any (fun b => decide (a = b))

/-- `arrMem` is sound for list membership. -/
theorem arrMem_sound {a : Arr} {arrays : List Arr} (h : arrMem a arrays = true) :
    a ∈ arrays := by
  unfold arrMem at h
  rcases List.any_eq_true.mp h with ⟨b, hb, hab⟩
  have hab' : a = b := of_decide_eq_true hab
  simpa [hab'] using hb

/-- Expression transfer restricted to the program support. Unknown variables
and arrays become `top`. -/
def evalExprAbsOn (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr)
    (abs : Abs) : Expr → Interval
  | .const n => toInterval n
  | .var x => if varMem x vars then abs.vars x else top
  | .add l r => add (evalExprAbsOn lengths vars arrays abs l)
      (evalExprAbsOn lengths vars arrays abs r)
  | .sub l r => sub (evalExprAbsOn lengths vars arrays abs l)
      (evalExprAbsOn lengths vars arrays abs r)
  | .mul _ _ => top
  | .div l r => div (evalExprAbsOn lengths vars arrays abs l) (evalExprAbsOn lengths vars arrays abs r)
  | .read a _ => if arrMem a arrays then abs.mem a else top
  | .len a => if arrMem a arrays then lenInterval lengths a else top

/-- Assignment over the restricted evaluator. -/
def assignAbsOn (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr)
    (abs : Abs) (x : Var) (e : Expr) : Abs :=
  { abs with vars := funUpdate abs.vars x (evalExprAbsOn lengths vars arrays abs e) }

/-- Store: the written array's interval becomes `top`. The index is not used
here; its bounds are a separate safety obligation. A join-with-value refinement
is deferred (the shared-join proof needs `Array.getD`/`set` lemmas that are not
part of M2.8). -/
def storeAbsOn (_lengths : Arr → Nat) (_vars : List Var) (_arrays : List Arr)
    (abs : Abs) (a : Arr) (_e : Expr) : Abs :=
  { abs with mem := fun a' => if a' = a then top else abs.mem a' }

/-- Empty-support top: all variables and arrays are `top`. -/
def topAbs : Abs :=
  { vars := fun _ => top, mem := fun _ => top }

/-- Inclusion over the captured program lists. -/
def bleAbs (vars : List Var) (arrays : List Arr) (a b : Abs) : Bool :=
  vars.all (fun x => ble (a.vars x) (b.vars x)) &&
  arrays.all (fun a' => ble (a.mem a') (b.mem a'))

/-- Pointwise join. -/
def joinAbs (a b : Abs) : Abs :=
  { vars := fun x => join (a.vars x) (b.vars x),
    mem := fun a' => join (a.mem a') (b.mem a') }

/-! ## Soundness -/

theorem evalExprAbsOn_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {e : Expr} {v : I32}
    (hs : GammaOn lengths vars arrays abs s) (h : eval e s = some v) :
    gamma (evalExprAbsOn lengths vars arrays abs e) v := by
  induction e generalizing v with
  | const n =>
      simp only [eval] at h
      cases h
      simp [evalExprAbsOn]
  | var x =>
      simp only [eval] at h
      cases h
      cases hx : varMem x vars with
      | false => simp [evalExprAbsOn, hx]
      | true => simpa [evalExprAbsOn, hx] using hs.1 x (varMem_sound hx)
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
  | mul l r ihl ihr => simp [evalExprAbsOn]
  | div l r ihl ihr =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨v1, h1, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨v2, h2l, h2r⟩
      exact div_sound (ihl h1) (ihr h2l) h2r
  | read a i ihi =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨idx, hidx, hrest⟩
      cases ha : arrMem a arrays with
      | false => simp [evalExprAbsOn, ha]
      | true =>
          simp only [evalExprAbsOn, ha, ite_true]
          split at hrest
          · rename_i hcond
            cases hrest
            have hnonneg : 0 ≤ idx.val := hcond.1
            have hlt : idx.val.toNat < (s.memAt a).size := by
              have hcast : (idx.val.toNat : Int) = idx.val := Int.toNat_of_nonneg hnonneg
              omega
            simpa using hs.2.2 a (arrMem_sound ha) idx.val.toNat hlt
          · simp at hrest
  | len a =>
      simp only [eval] at h
      cases ha : arrMem a arrays with
      | false => simp [evalExprAbsOn, ha]
      | true =>
          simp only [evalExprAbsOn, ha, ite_true]
          have hlen : (s.memAt a).size = lengths a := hs.2.1 a (arrMem_sound ha)
          rw [hlen] at h
          cases hof : I32.ofInt? (lengths a : Int) with
          | none => simp [hof] at h
          | some n =>
              have hn : n = v := by simpa [hof] using h
              subst n
              simp [lenInterval, hof]

theorem topAbs_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {s : State} (hP : POn lengths s) :
    GammaOn lengths vars arrays topAbs s := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp [topAbs]
  · intro a ha
    exact hP a
  · intro a ha i hi
    simp [topAbs]

theorem bleAbs_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {a b : Abs} {s : State}
    (h : bleAbs vars arrays a b = true) (hP : POn lengths s)
    (hga : GammaOn lengths vars arrays a s) :
    GammaOn lengths vars arrays b s := by
  have h' : vars.all (fun x => ble (a.vars x) (b.vars x)) = true ∧
      arrays.all (fun a' => ble (a.mem a') (b.mem a')) = true := by
    simpa [bleAbs] using h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxble : ble (a.vars x) (b.vars x) = true :=
      List.all_eq_true.mp h'.1 x hx
    exact ble_sound hxble (s.get x) (hga.1 x hx)
  · intro a' ha
    exact hP a'
  · intro a' ha i hi
    have hable : ble (a.mem a') (b.mem a') = true :=
      List.all_eq_true.mp h'.2 a' ha
    exact ble_sound hable ((s.memAt a').getD i I32.zero)
      (hga.2.2 a' ha i hi)

theorem joinAbs_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {a b : Abs} {s : State}
    (hP : POn lengths s) (h : GammaOn lengths vars arrays a s ∨
      GammaOn lengths vars arrays b s) :
    GammaOn lengths vars arrays (joinAbs a b) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases h with h | h
    · simpa [joinAbs] using join_sound (Or.inl (h.1 x hx))
    · simpa [joinAbs] using join_sound (Or.inr (h.1 x hx))
  · intro a' ha
    exact hP a'
  · intro a' ha i hi
    rcases h with h | h
    · simpa [joinAbs] using join_sound (Or.inl (h.2.2 a' ha i hi))
    · simpa [joinAbs] using join_sound (Or.inr (h.2.2 a' ha i hi))

theorem assignAbsOn_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {x : Var} {e : Expr} {v : I32}
    (hs : GammaOn lengths vars arrays abs s) (h : eval e s = some v) :
    GammaOn lengths vars arrays (assignAbsOn lengths vars arrays abs x e)
      (s.set x v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst y
      have he := evalExprAbsOn_sound hs h
      simpa [assignAbsOn, State.set, State.get, funUpdate] using he
    · simpa [assignAbsOn, State.set, State.get, funUpdate, hyx] using hs.1 y hy
  · intro a ha
    simpa [State.set, State.memAt] using hs.2.1 a ha
  · intro a ha i hi
    simpa [assignAbsOn, State.set, State.memAt] using hs.2.2 a ha i hi

/-- Store keeps `GammaOn`: the written array is `top`, so every cell of the new
array is covered. Lengths are preserved by `Array.set`. -/
theorem storeAbsOn_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {a : Arr} {e : Expr}
    {idx val : I32}
    (hP : POn lengths s) (hs : GammaOn lengths vars arrays abs s)
    (hbound : 0 ≤ idx.val ∧ idx.val < ((s.memAt a).size : Int)) :
    GammaOn lengths vars arrays (storeAbsOn lengths vars arrays abs a e)
      (s.setMem a ((s.memAt a).set idx.val.toNat val)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa [storeAbsOn, State.setMem, State.get] using hs.1 x hx
  · intro b hb
    by_cases hba : b = a
    · subst b
      have hmem : (s.setMem a ((s.memAt a).set idx.val.toNat val)).memAt a =
          (s.memAt a).set idx.val.toNat val := by
        simp [State.setMem, State.memAt, funUpdate]
      rw [hmem]
      rw [Array.size_set (by
        have hcast : (idx.val.toNat : Int) = idx.val := Int.toNat_of_nonneg hbound.1
        omega)]
      exact hP a
    · have hmem : (s.setMem a ((s.memAt a).set idx.val.toNat val)).memAt b =
          s.memAt b := by
        simp [State.setMem, State.memAt, funUpdate, hba]
      rw [hmem]
      exact hs.2.1 b hb
  · intro b hb j hj
    by_cases hba : b = a
    · subst b
      simp [storeAbsOn]
    · have hmem : (s.setMem a ((s.memAt a).set idx.val.toNat val)).memAt b =
          s.memAt b := by
        simp [State.setMem, State.memAt, funUpdate, hba]
      rw [hmem] at hj ⊢
      simpa [storeAbsOn, hba] using hs.2.2 b hb j hj

/-! ### Guard refinement (F3)

The `assume` edge sharpens the variable in a single-variable comparison:
`x < c` true becomes `meet i (-∞, c-1]`, `x ≥ c` false becomes the same, and so
on. Conjunctions refine left-to-right; disjunctions and non-variable comparisons
are left unchanged (sound, less precise). -/

/-- `c - 1`, or `none` if that underflows. -/
def predI32? (c : I32) : Option I32 := I32.sub? c I32.one

/-- `c + 1`, or `none` if that overflows. -/
def succI32? (c : I32) : Option I32 := I32.add? c I32.one

def restrictHi (i : Interval) (c : I32) : Interval :=
  meet i (ofBounds none (some c))

def restrictLo (i : Interval) (c : I32) : Interval :=
  meet i (ofBounds (some c) none)

def restrictEq (i : Interval) (c : I32) : Interval :=
  meet i (toInterval c)

/-- `x < c` true: clamp above by `c - 1`; `bot` when `c` is `i32Min`. -/
def restrictHiPred (i : Interval) (c : I32) : Interval :=
  match predI32? c with
  | some c' => restrictHi i c'
  | none => .bot

/-- `x > c` true: clamp below by `c + 1`; `bot` when `c` is `i32Max`. -/
def restrictLoSucc (i : Interval) (c : I32) : Interval :=
  match succI32? c with
  | some c' => restrictLo i c'
  | none => .bot

/-- Refine a single interval by a comparison with a constant. -/
def refineVar (i : Interval) (op : CmpOp) (c : I32) (positive : Bool) : Interval :=
  match op, positive with
  | .lt, true => restrictHiPred i c
  | .lt, false => restrictLo i c
  | .le, true => restrictHi i c
  | .le, false => restrictLoSucc i c
  | .gt, true => restrictLoSucc i c
  | .gt, false => restrictHi i c
  | .ge, true => restrictLo i c
  | .ge, false => restrictHiPred i c
  | .eq, true => restrictEq i c
  | .eq, false => i
  | .ne, true => i
  | .ne, false => restrictEq i c

/-- Swap the operands of a comparison. -/
def swapCmp : CmpOp → CmpOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le

/-- Refine an abstract state by a condition and its polarity. -/
def refineAbs (vars : List Var) (abs : Abs) (b : BExp) (positive : Bool) : Abs :=
  match b with
  | .cmp op (.var x) (.const c) =>
      if varMem x vars then
        { abs with vars := funUpdate abs.vars x (refineVar (abs.vars x) op c positive) }
      else abs
  | .cmp op (.const c) (.var x) =>
      if varMem x vars then
        { abs with vars := funUpdate abs.vars x (refineVar (abs.vars x) (swapCmp op) c positive) }
      else abs
  | .and l r =>
      if positive then refineAbs vars (refineAbs vars abs l true) r true else abs
  | .not b => refineAbs vars abs b (!positive)
  | _ => abs

theorem restrictHi_sound {i : Interval} {c v : I32}
    (hi : gamma i v) (hv : v.val ≤ c.val) : gamma (restrictHi i c) v := by
  apply meet_sound hi
  apply gamma_ofBounds_of_lower_upper
  · exact lowerOk_none v
  · exact (upperOk_some c v).2 hv

theorem restrictLo_sound {i : Interval} {c v : I32}
    (hi : gamma i v) (hv : c.val ≤ v.val) : gamma (restrictLo i c) v := by
  apply meet_sound hi
  apply gamma_ofBounds_of_lower_upper
  · exact (lowerOk_some c v).2 hv
  · exact upperOk_none v

theorem restrictEq_sound {i : Interval} {c v : I32}
    (hi : gamma i v) (hv : v = c) : gamma (restrictEq i c) v := by
  subst v
  exact meet_sound hi (gamma_toInterval c)

theorem restrictHiPred_sound {i : Interval} {c v : I32}
    (hi : gamma i v) (hv : v.val < c.val) : gamma (restrictHiPred i c) v := by
  unfold restrictHiPred
  cases h : predI32? c
  · exfalso
    unfold predI32? at h
    have hnone := I32.sub?_none_iff.mp h
    have hcmin' : i32Min ≤ c.val := c.min_le
    have hcmax' : c.val ≤ i32Max := c.le_max
    have hcmin : c.val = i32Min := by
      have hlt : c.val - 1 < i32Min := by
        by_cases hge : i32Min ≤ c.val - 1
        · have hle : c.val - 1 ≤ i32Max := by omega
          exact absurd ⟨hge, hle⟩ hnone
        · omega
      omega
    have hvmin : i32Min ≤ v.val := v.min_le
    omega
  · rename_i c'
    have hc' : c'.val = c.val - 1 := by
      exact I32.sub?_sound (by simpa [predI32?] using h)
    apply restrictHi_sound hi
    omega

theorem restrictLoSucc_sound {i : Interval} {c v : I32}
    (hi : gamma i v) (hv : c.val < v.val) : gamma (restrictLoSucc i c) v := by
  unfold restrictLoSucc
  cases h : succI32? c
  · exfalso
    unfold succI32? at h
    have hnone := I32.add?_none_iff.mp h
    have hcmin' : i32Min ≤ c.val := c.min_le
    have hcmax' : c.val ≤ i32Max := c.le_max
    have hcmax : c.val = i32Max := by
      have hgt : i32Max < c.val + 1 := by
        by_cases hle : c.val + 1 ≤ i32Max
        · have hge : i32Min ≤ c.val + 1 := by omega
          exact absurd ⟨hge, hle⟩ hnone
        · omega
      omega
    have hvmax : v.val ≤ i32Max := v.le_max
    omega
  · rename_i c'
    have hc' : c'.val = c.val + 1 := by
      exact I32.add?_sound (by simpa [succI32?] using h)
    apply restrictLo_sound hi
    omega

theorem compare_swap (op : CmpOp) (a b : I32) :
    compare (swapCmp op) a b = compare op b a := by
  cases op with
  | eq =>
      by_cases hab : a.val = b.val
      · have hba : b.val = a.val := hab.symm
        simp [swapCmp, compare, decide_eq_true_eq.mpr hab, decide_eq_true_eq.mpr hba]
      · have hba : ¬ b.val = a.val := fun h => hab h.symm
        simp [swapCmp, compare, decide_eq_false_iff_not.mpr hab,
          decide_eq_false_iff_not.mpr hba]
  | ne =>
      by_cases hab : a.val = b.val
      · have hne : ¬ a.val ≠ b.val := fun h => h hab
        have hne' : ¬ b.val ≠ a.val := fun h => h hab.symm
        simp [swapCmp, compare, decide_eq_false_iff_not.mpr hne,
          decide_eq_false_iff_not.mpr hne']
      · have hne : a.val ≠ b.val := hab
        have hne' : b.val ≠ a.val := fun h => hab h.symm
        simp [swapCmp, compare, decide_eq_true_eq.mpr hne,
          decide_eq_true_eq.mpr hne']
  | lt => rfl
  | le => rfl
  | gt => rfl
  | ge => rfl

theorem refineVar_sound {i : Interval} {v c : I32} {op : CmpOp} {positive : Bool}
    (hi : gamma i v) (hc : compare op v c = positive) :
    gamma (refineVar i op c positive) v := by
  cases op with
  | eq =>
      cases positive with
      | true =>
          have hv : v = c :=
            I32.ext (of_decide_eq_true (show decide (v.val = c.val) = true from hc))
          change gamma (restrictEq i c) v
          exact restrictEq_sound hi hv
      | false =>
          change gamma i v
          exact hi
  | ne =>
      cases positive with
      | true =>
          change gamma i v
          exact hi
      | false =>
          have hv : v = c := by
            have hne : ¬ v.val ≠ c.val :=
              of_decide_eq_false (show decide (v.val ≠ c.val) = false from hc)
            by_cases hvc : v.val = c.val
            · exact I32.ext hvc
            · exfalso
              exact hne hvc
          change gamma (restrictEq i c) v
          exact restrictEq_sound hi hv
  | lt =>
      cases positive with
      | true =>
          have hv : v.val < c.val :=
            of_decide_eq_true (show decide (v.val < c.val) = true from hc)
          change gamma (restrictHiPred i c) v
          exact restrictHiPred_sound hi hv
      | false =>
          have hv : ¬ v.val < c.val :=
            of_decide_eq_false (show decide (v.val < c.val) = false from hc)
          have hle : c.val ≤ v.val := by omega
          change gamma (restrictLo i c) v
          exact restrictLo_sound hi hle
  | le =>
      cases positive with
      | true =>
          have hv : v.val ≤ c.val :=
            of_decide_eq_true (show decide (v.val ≤ c.val) = true from hc)
          change gamma (restrictHi i c) v
          exact restrictHi_sound hi hv
      | false =>
          have hv : ¬ v.val ≤ c.val :=
            of_decide_eq_false (show decide (v.val ≤ c.val) = false from hc)
          have hlt : c.val < v.val := by omega
          change gamma (restrictLoSucc i c) v
          exact restrictLoSucc_sound hi hlt
  | gt =>
      cases positive with
      | true =>
          have hv : c.val < v.val :=
            of_decide_eq_true (show decide (c.val < v.val) = true from hc)
          change gamma (restrictLoSucc i c) v
          exact restrictLoSucc_sound hi hv
      | false =>
          have hv : ¬ c.val < v.val :=
            of_decide_eq_false (show decide (c.val < v.val) = false from hc)
          have hle : v.val ≤ c.val := by omega
          change gamma (restrictHi i c) v
          exact restrictHi_sound hi hle
  | ge =>
      cases positive with
      | true =>
          have hv : c.val ≤ v.val :=
            of_decide_eq_true (show decide (c.val ≤ v.val) = true from hc)
          change gamma (restrictLo i c) v
          exact restrictLo_sound hi hv
      | false =>
          have hv : ¬ c.val ≤ v.val :=
            of_decide_eq_false (show decide (c.val ≤ v.val) = false from hc)
          have hlt : v.val < c.val := by omega
          change gamma (restrictHiPred i c) v
          exact restrictHiPred_sound hi hlt

theorem refineAbs_sound {lengths : Arr → Nat} {vars : List Var} {arrays : List Arr}
    {abs : Abs} {b : BExp} {positive : Bool} {s : State}
    (hs : GammaOn lengths vars arrays abs s) (hb : evalB b s = some positive) :
    GammaOn lengths vars arrays (refineAbs vars abs b positive) s := by
  induction b generalizing abs positive with
  | cmp op l r =>
      cases l with
      | var x =>
          cases r with
          | const c =>
              cases hx : varMem x vars with
              | false =>
                  simp [refineAbs, hx]
                  exact hs
              | true =>
                  simp only [refineAbs, hx, ite_true]
                  refine ⟨?_, ?_, ?_⟩
                  · intro y hy
                    by_cases hyx : y = x
                    · subst y
                      have hcmp : compare op (s.get x) c = positive := by
                        simpa [evalB, eval] using hb
                      simpa [funUpdate] using
                        refineVar_sound (hs.1 x (varMem_sound hx)) hcmp
                    · simpa [funUpdate, hyx] using hs.1 y hy
                  · intro a ha
                    simpa using hs.2.1 a ha
                  · intro a ha i hi
                    simpa using hs.2.2 a ha i hi
          | _ =>
              simp [refineAbs]
              exact hs
      | const c =>
          cases r with
          | var x =>
              cases hx : varMem x vars with
              | false =>
                  simp [refineAbs, hx]
                  exact hs
              | true =>
                  simp only [refineAbs, hx, ite_true]
                  refine ⟨?_, ?_, ?_⟩
                  · intro y hy
                    by_cases hyx : y = x
                    · subst y
                      have hcmp : compare op c (s.get x) = positive := by
                        simpa [evalB, eval] using hb
                      have hcmp' : compare (swapCmp op) (s.get x) c = positive := by
                        rw [compare_swap]
                        exact hcmp
                      simpa [funUpdate] using
                        refineVar_sound (hs.1 x (varMem_sound hx)) hcmp'
                    · simpa [funUpdate, hyx] using hs.1 y hy
                  · intro a ha
                    simpa using hs.2.1 a ha
                  · intro a ha i hi
                    simpa using hs.2.2 a ha i hi
          | _ =>
              simp [refineAbs]
              exact hs
      | _ =>
          simp [refineAbs]
          exact hs
  | and l r ihl ihr =>
      cases positive with
      | false =>
          simp [refineAbs]
          exact hs
      | true =>
          simp only [refineAbs]
          have hb' : evalB l s = some true ∧ evalB r s = some true := by
            simp only [evalB] at hb
            rcases Option.bind_eq_some_iff.mp hb with ⟨a, ha, h2⟩
            rcases Option.bind_eq_some_iff.mp h2 with ⟨b, hb2, hres⟩
            injection hres with hab
            have hab' : a = true ∧ b = true := by simpa using hab
            rcases hab' with ⟨rfl, rfl⟩
            exact ⟨ha, hb2⟩
          rcases hb' with ⟨hl, hr⟩
          simpa using ihr (ihl hs hl) hr
  | not b ih =>
      have hb' : evalB b s = some (!positive) := by
        cases hbe : evalB b s with
        | none => simp [evalB, hbe] at hb
        | some x =>
            simp only [evalB, hbe] at hb
            injection hb with hx
            have hx' : x = !positive := by simpa using congrArg Bool.not hx
            simp [hx']
      simpa [refineAbs] using ih hs hb'
  | or l r ihl ihr =>
      simp [refineAbs]
      exact hs

/-! ## Edge transfer and the `CertDomain` instance -/

/-- Transfer a checker edge. Stores set the written array to `top`; guards and
asserts do not refine here (guard refinement is a later domain refinement). -/
def transferAbs (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr) :
    EdgeCmd → Abs → Abs
  | .atomic .skip, abs => abs
  | .atomic (.assign x e), abs => assignAbsOn lengths vars arrays abs x e
  | .atomic (.store a _ e), abs => storeAbsOn lengths vars arrays abs a e
  | .atomic (.assert _), abs => abs
  | .assume b true, abs => refineAbs vars abs b true
  | .assume b false, abs => refineAbs vars abs b false

theorem transferAbs_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {c : EdgeCmd} {abs : Abs} {s s' : State}
    (hP : POn lengths s) (hg : GammaOn lengths vars arrays abs s)
    (h : EdgeCmd.exec c s = some s')
    (_hP' : POn lengths s') :
    GammaOn lengths vars arrays (transferAbs lengths vars arrays c abs) s' := by
  cases c with
  | atomic cmd =>
      cases cmd with
      | skip =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          cases h
          simpa [transferAbs] using hg
      | assign x e =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨v, he, hset⟩
          cases hset
          simpa [transferAbs] using assignAbsOn_sound hg he
      | store a i e =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨idx, hi, h2⟩
          rcases Option.bind_eq_some_iff.mp h2 with ⟨val, hv, h3⟩
          split at h3
          · rename_i hbound
            cases h3
            simpa [transferAbs] using storeAbsOn_sound hP hg hbound
          · simp at h3
      | assert b =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨v, hv, hif⟩
          split at hif
          · cases hif
            simpa [transferAbs] using hg
          · simp at hif
  | assume b p =>
      cases p
      · simp only [EdgeCmd.exec] at h
        split at h
        · rename_i hb
          cases h
          simpa [transferAbs] using refineAbs_sound hg hb
        · simp at h
      · simp only [EdgeCmd.exec] at h
        split at h
        · rename_i hb
          cases h
          simpa [transferAbs] using refineAbs_sound hg hb
        · simp at h

/-! ## Checker interface: initial state, entailment, and `P` preservation (F1)

The three operations the checker needs beyond the M2 soundness fields:
`initOf`/`init_sound` (the base case), `entails`/`entails_sound` (the safety
obligations), and `P_step` (the induction invariant). `bot` is deliberately not
a domain field: the checker represents a certificate's explicit unreachable
state as `Option Abs`, so the domain never needs an all-`bot` element (see the
note at the end of `Domain.lean`).
-/

/-! ### Endpoint extraction -/

theorem addLower?_some_some {lo1 lo2 : Option I32} {lo' : I32}
    (h : addLower? lo1 lo2 = some (some lo')) :
    ∃ a b, lo1 = some a ∧ lo2 = some b ∧ lo'.val = a.val + b.val := by
  cases lo1 with
  | none => simp [addLower?] at h
  | some a =>
    cases lo2 with
    | none => simp [addLower?] at h
    | some b =>
      simp only [addLower?] at h
      rcases Option.map_eq_some_iff.mp h with ⟨c, hc, hEq⟩
      have hc' : c = lo' := by simpa using hEq
      subst c
      exact ⟨a, b, rfl, rfl, I32.add?_sound hc⟩

theorem addUpper?_some_some {hi1 hi2 : Option I32} {hi' : I32}
    (h : addUpper? hi1 hi2 = some (some hi')) :
    ∃ c d, hi1 = some c ∧ hi2 = some d ∧ hi'.val = c.val + d.val := by
  cases hi1 with
  | none => simp [addUpper?] at h
  | some c =>
    cases hi2 with
    | none => simp [addUpper?] at h
    | some d =>
      simp only [addUpper?] at h
      rcases Option.map_eq_some_iff.mp h with ⟨e, he, hEq⟩
      have he' : e = hi' := by simpa using hEq
      subst e
      exact ⟨c, d, rfl, rfl, I32.add?_sound he⟩

theorem subLower?_some_some {lo1 hi2 : Option I32} {lo' : I32}
    (h : subLower? lo1 hi2 = some (some lo')) :
    ∃ a d, lo1 = some a ∧ hi2 = some d ∧ lo'.val = a.val - d.val := by
  cases lo1 with
  | none => simp [subLower?] at h
  | some a =>
    cases hi2 with
    | none => simp [subLower?] at h
    | some d =>
      simp only [subLower?] at h
      rcases Option.map_eq_some_iff.mp h with ⟨c, hc, hEq⟩
      have hc' : c = lo' := by simpa using hEq
      subst c
      exact ⟨a, d, rfl, rfl, I32.sub?_sound hc⟩

theorem subUpper?_some_some {hi1 lo2 : Option I32} {hi' : I32}
    (h : subUpper? hi1 lo2 = some (some hi')) :
    ∃ c b, hi1 = some c ∧ lo2 = some b ∧ hi'.val = c.val - b.val := by
  cases hi1 with
  | none => simp [subUpper?] at h
  | some c =>
    cases lo2 with
    | none => simp [subUpper?] at h
    | some b =>
      simp only [subUpper?] at h
      rcases Option.map_eq_some_iff.mp h with ⟨e, he, hEq⟩
      have he' : e = hi' := by simpa using hEq
      subst e
      exact ⟨c, b, rfl, rfl, I32.sub?_sound he⟩

/-! ### Guarded endpoint arithmetic -/

/-- Abstract addition that returns `some` only when both endpoint sums are
finite, so every concrete addition it represents is defined. -/
def addGuarded : Interval → Interval → Option Interval
  | .bot, _ => some .bot
  | _, .bot => some .bot
  | .itv lo1 hi1 _, .itv lo2 hi2 _ =>
      match addLower? lo1 lo2, addUpper? hi1 hi2 with
      | some (some lo), some (some hi) => some (ofBounds (some lo) (some hi))
      | _, _ => none

/-- Abstract subtraction under the same definedness discipline. -/
def subGuarded : Interval → Interval → Option Interval
  | .bot, _ => some .bot
  | _, .bot => some .bot
  | .itv lo1 hi1 _, .itv lo2 hi2 _ =>
      match subLower? lo1 hi2, subUpper? hi1 lo2 with
      | some (some lo), some (some hi) => some (ofBounds (some lo) (some hi))
      | _, _ => none

theorem addGuarded_sound {il ir i : Interval}
    (h : addGuarded il ir = some i) {v1 v2 : I32}
    (h1 : gamma il v1) (h2 : gamma ir v2) :
    ∃ v, I32.add? v1 v2 = some v ∧ gamma i v := by
  cases il with
  | bot => simp [gamma] at h1
  | itv lo1 hi1 w1 =>
    cases ir with
    | bot => simp [gamma] at h2
    | itv lo2 hi2 w2 =>
      have h1' : lowerOk lo1 v1 ∧ upperOk hi1 v1 := by simpa [gamma] using h1
      have h2' : lowerOk lo2 v2 ∧ upperOk hi2 v2 := by simpa [gamma] using h2
      simp only [addGuarded] at h
      cases hL : addLower? lo1 lo2 with
      | none => simp [hL] at h
      | some lo =>
        cases hU : addUpper? hi1 hi2 with
        | none => simp [hL, hU] at h
        | some hi =>
          cases lo with
          | none => simp [hL, hU] at h
          | some lo' =>
            cases hi with
            | none => simp [hL, hU] at h
            | some hi' =>
              simp only [hL, hU] at h
              cases h
              rcases addLower?_some_some hL with ⟨a, b, rfl, rfl, hlo⟩
              rcases addUpper?_some_some hU with ⟨c, d, rfl, rfl, hhi⟩
              have ha : a.val ≤ v1.val := (lowerOk_some a v1).1 h1'.1
              have hc : v1.val ≤ c.val := (upperOk_some c v1).1 h1'.2
              have hb : b.val ≤ v2.val := (lowerOk_some b v2).1 h2'.1
              have hd : v2.val ≤ d.val := (upperOk_some d v2).1 h2'.2
              have hlo_range : i32Min ≤ lo'.val := lo'.min_le
              have hhi_range : hi'.val ≤ i32Max := hi'.le_max
              have hsome : (I32.add? v1 v2).isSome = true := by
                rw [I32.add?_isSome_iff]
                constructor <;> omega
              rcases Option.isSome_iff_exists.mp hsome with ⟨v, hv⟩
              have hvs : v.val = v1.val + v2.val := I32.add?_sound hv
              refine ⟨v, hv, ?_⟩
              apply gamma_ofBounds_of_lower_upper
              · exact (lowerOk_some lo' v).2 (by omega)
              · exact (upperOk_some hi' v).2 (by omega)

theorem subGuarded_sound {il ir i : Interval}
    (h : subGuarded il ir = some i) {v1 v2 : I32}
    (h1 : gamma il v1) (h2 : gamma ir v2) :
    ∃ v, I32.sub? v1 v2 = some v ∧ gamma i v := by
  cases il with
  | bot => simp [gamma] at h1
  | itv lo1 hi1 w1 =>
    cases ir with
    | bot => simp [gamma] at h2
    | itv lo2 hi2 w2 =>
      have h1' : lowerOk lo1 v1 ∧ upperOk hi1 v1 := by simpa [gamma] using h1
      have h2' : lowerOk lo2 v2 ∧ upperOk hi2 v2 := by simpa [gamma] using h2
      simp only [subGuarded] at h
      cases hL : subLower? lo1 hi2 with
      | none => simp [hL] at h
      | some lo =>
        cases hU : subUpper? hi1 lo2 with
        | none => simp [hL, hU] at h
        | some hi =>
          cases lo with
          | none => simp [hL, hU] at h
          | some lo' =>
            cases hi with
            | none => simp [hL, hU] at h
            | some hi' =>
              simp only [hL, hU] at h
              cases h
              rcases subLower?_some_some hL with ⟨a, d, rfl, rfl, hlo⟩
              rcases subUpper?_some_some hU with ⟨c, b, rfl, rfl, hhi⟩
              have ha : a.val ≤ v1.val := (lowerOk_some a v1).1 h1'.1
              have hc : v1.val ≤ c.val := (upperOk_some c v1).1 h1'.2
              have hb : b.val ≤ v2.val := (lowerOk_some b v2).1 h2'.1
              have hd : v2.val ≤ d.val := (upperOk_some d v2).1 h2'.2
              have hlo_range : i32Min ≤ lo'.val := lo'.min_le
              have hhi_range : hi'.val ≤ i32Max := hi'.le_max
              have hsome : (I32.sub? v1 v2).isSome = true := by
                rw [I32.sub?_isSome_iff]
                constructor <;> omega
              rcases Option.isSome_iff_exists.mp hsome with ⟨v, hv⟩
              have hvs : v.val = v1.val - v2.val := I32.sub?_sound hv
              refine ⟨v, hv, ?_⟩
              apply gamma_ofBounds_of_lower_upper
              · exact (lowerOk_some lo' v).2 (by omega)
              · exact (upperOk_some hi' v).2 (by omega)

/-! ### Guarded expression evaluation -/

/-- Evaluation that returns `some i` only when the expression is guaranteed to
evaluate and its value lies in `i`. `+`/`-` use the guarded endpoint
arithmetic; `len` is exact when the array is in support; multiplication,
division and array reads remain `none` (conservative: `entails` declines to
certify them). -/
def evalExprGuarded (_lengths : Arr → Nat) (_vars : List Var) (_arrays : List Arr)
    (abs : Abs) : Expr → Option Interval
  | .const n => some (toInterval n)
  | .var x => if varMem x _vars then some (abs.vars x) else none
  | .add l r =>
      evalExprGuarded _lengths _vars _arrays abs l >>= fun il =>
      evalExprGuarded _lengths _vars _arrays abs r >>= fun ir =>
        addGuarded il ir
  | .sub l r =>
      evalExprGuarded _lengths _vars _arrays abs l >>= fun il =>
      evalExprGuarded _lengths _vars _arrays abs r >>= fun ir =>
        subGuarded il ir
  | .mul _ _ => none
  | .div _ _ => none
  | .read _ _ => none
  | .len a =>
      if arrMem a _arrays then
        match I32.ofInt? (_lengths a : Int) with
        | some n => some (toInterval n)
        | none => none
      else none

theorem evalExprGuarded_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {e : Expr} {i : Interval}
    (h : evalExprGuarded lengths vars arrays abs e = some i)
    (hs : GammaOn lengths vars arrays abs s) :
    ∃ v, eval e s = some v ∧ gamma i v := by
  induction e generalizing i with
  | const n =>
      simp only [evalExprGuarded] at h
      cases h
      exact ⟨n, rfl, gamma_toInterval n⟩
  | var x =>
      simp only [evalExprGuarded] at h
      cases hx : varMem x vars with
      | false => simp [hx] at h
      | true =>
          simp [hx] at h
          cases h
          exact ⟨s.get x, rfl, hs.1 x (varMem_sound hx)⟩
  | add l r ihl ihr =>
      simp only [evalExprGuarded] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨il, hl, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨ir, hr, h3⟩
      rcases ihl hl with ⟨v1, he1, hg1⟩
      rcases ihr hr with ⟨v2, he2, hg2⟩
      rcases addGuarded_sound h3 hg1 hg2 with ⟨v, hadd, hg⟩
      refine ⟨v, ?_, hg⟩
      simp [eval, he1, he2, hadd]
  | sub l r ihl ihr =>
      simp only [evalExprGuarded] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨il, hl, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨ir, hr, h3⟩
      rcases ihl hl with ⟨v1, he1, hg1⟩
      rcases ihr hr with ⟨v2, he2, hg2⟩
      rcases subGuarded_sound h3 hg1 hg2 with ⟨v, hsub, hg⟩
      refine ⟨v, ?_, hg⟩
      simp [eval, he1, he2, hsub]
  | mul _ _ => simp [evalExprGuarded] at h
  | div _ _ => simp [evalExprGuarded] at h
  | read _ _ => simp [evalExprGuarded] at h
  | len a =>
      simp only [evalExprGuarded] at h
      by_cases ha : arrMem a arrays
      · simp [ha] at h
        cases hof : I32.ofInt? (lengths a : Int) with
        | none => simp [hof] at h
        | some n =>
            simp [hof] at h
            cases h
            have hlen : (s.memAt a).size = lengths a := hs.2.1 a (arrMem_sound ha)
            refine ⟨n, ?_, gamma_toInterval n⟩
            simp [eval, hlen, hof]
      · simp [ha] at h

/-! ### Guarded comparisons and boolean entailment -/

/-- `eq` for two intervals: `some true`/`some false` only when every pair of
represented values compares that way. `bot` is vacuously true. -/
def eqGuarded : Interval → Interval → Option Bool
  | .bot, _ => some true
  | _, .bot => some true
  | .itv (some a1) (some b1) _, .itv (some a2) (some b2) _ =>
      if a1.val = b1.val ∧ a2.val = b2.val then
        if a1.val = a2.val then some true else some false
      else if b1.val < a2.val ∨ b2.val < a1.val then some false else none
  | _, _ => none

/-- `lt` for two finite intervals. -/
def ltGuarded : Interval → Interval → Option Bool
  | .bot, _ => some true
  | _, .bot => some true
  | .itv (some lo1) (some hi1) _, .itv (some lo2) (some hi2) _ =>
      if hi1.val < lo2.val then some true
      else if hi2.val ≤ lo1.val then some false
      else none
  | _, _ => none

/-- `le` for two finite intervals. -/
def leGuarded : Interval → Interval → Option Bool
  | .bot, _ => some true
  | _, .bot => some true
  | .itv (some lo1) (some hi1) _, .itv (some lo2) (some hi2) _ =>
      if hi1.val ≤ lo2.val then some true
      else if hi2.val < lo1.val then some false
      else none
  | _, _ => none

theorem eqGuarded_sound {a b : Interval} {r : Bool}
    (h : eqGuarded a b = some r) {v1 v2 : I32}
    (h1 : gamma a v1) (h2 : gamma b v2) :
    compare .eq v1 v2 = r := by
  cases a with
  | bot => simp [gamma] at h1
  | itv lo1 hi1 w1 =>
    cases b with
    | bot => simp [gamma] at h2
    | itv lo2 hi2 w2 =>
      cases lo1 with
      | none => simp [eqGuarded] at h
      | some a1 =>
        cases hi1 with
        | none => simp [eqGuarded] at h
        | some b1 =>
          cases lo2 with
          | none => simp [eqGuarded] at h
          | some a2 =>
            cases hi2 with
            | none => simp [eqGuarded] at h
            | some b2 =>
              have hg1 : lowerOk (some a1) v1 ∧ upperOk (some b1) v1 := by
                simpa [gamma] using h1
              have hg2 : lowerOk (some a2) v2 ∧ upperOk (some b2) v2 := by
                simpa [gamma] using h2
              have ha1 : a1.val ≤ v1.val := (lowerOk_some a1 v1).1 hg1.1
              have hb1 : v1.val ≤ b1.val := (upperOk_some b1 v1).1 hg1.2
              have ha2 : a2.val ≤ v2.val := (lowerOk_some a2 v2).1 hg2.1
              have hb2 : v2.val ≤ b2.val := (upperOk_some b2 v2).1 hg2.2
              simp only [eqGuarded] at h
              split at h
              · rename_i hsingle
                split at h
                · rename_i heq
                  cases h
                  have hv1 : v1.val = a1.val := by omega
                  have hv2 : v2.val = a2.val := by omega
                  simp only [compare, hv1, hv2]
                  exact decide_eq_true_eq.mpr heq
                · rename_i hne
                  cases h
                  have hv1 : v1.val = a1.val := by omega
                  have hv2 : v2.val = a2.val := by omega
                  simp only [compare, hv1, hv2]
                  exact decide_eq_false_iff_not.mpr hne
              · rename_i hsingle
                split at h
                · rename_i hdisj
                  cases h
                  have hneq : v1.val ≠ v2.val := by
                    intro hveq
                    omega
                  simp only [compare]
                  exact decide_eq_false_iff_not.mpr hneq
                · simp at h

theorem ltGuarded_sound {a b : Interval} {r : Bool}
    (h : ltGuarded a b = some r) {v1 v2 : I32}
    (h1 : gamma a v1) (h2 : gamma b v2) :
    compare .lt v1 v2 = r := by
  cases a with
  | bot => simp [gamma] at h1
  | itv lo1 hi1 w1 =>
    cases b with
    | bot => simp [gamma] at h2
    | itv lo2 hi2 w2 =>
      cases lo1 with
      | none => simp [ltGuarded] at h
      | some a1 =>
        cases hi1 with
        | none => simp [ltGuarded] at h
        | some b1 =>
          cases lo2 with
          | none => simp [ltGuarded] at h
          | some a2 =>
            cases hi2 with
            | none => simp [ltGuarded] at h
            | some b2 =>
              have hg1 : lowerOk (some a1) v1 ∧ upperOk (some b1) v1 := by
                simpa [gamma] using h1
              have hg2 : lowerOk (some a2) v2 ∧ upperOk (some b2) v2 := by
                simpa [gamma] using h2
              have ha1 : a1.val ≤ v1.val := (lowerOk_some a1 v1).1 hg1.1
              have hb1 : v1.val ≤ b1.val := (upperOk_some b1 v1).1 hg1.2
              have ha2 : a2.val ≤ v2.val := (lowerOk_some a2 v2).1 hg2.1
              have hb2 : v2.val ≤ b2.val := (upperOk_some b2 v2).1 hg2.2
              simp only [ltGuarded] at h
              split at h
              · rename_i hlt
                cases h
                simp only [compare]
                exact decide_eq_true_eq.mpr (by omega)
              · split at h
                · rename_i hnlt
                  cases h
                  simp only [compare]
                  exact decide_eq_false_iff_not.mpr (by omega)
                · simp at h

theorem leGuarded_sound {a b : Interval} {r : Bool}
    (h : leGuarded a b = some r) {v1 v2 : I32}
    (h1 : gamma a v1) (h2 : gamma b v2) :
    compare .le v1 v2 = r := by
  cases a with
  | bot => simp [gamma] at h1
  | itv lo1 hi1 w1 =>
    cases b with
    | bot => simp [gamma] at h2
    | itv lo2 hi2 w2 =>
      cases lo1 with
      | none => simp [leGuarded] at h
      | some a1 =>
        cases hi1 with
        | none => simp [leGuarded] at h
        | some b1 =>
          cases lo2 with
          | none => simp [leGuarded] at h
          | some a2 =>
            cases hi2 with
            | none => simp [leGuarded] at h
            | some b2 =>
              have hg1 : lowerOk (some a1) v1 ∧ upperOk (some b1) v1 := by
                simpa [gamma] using h1
              have hg2 : lowerOk (some a2) v2 ∧ upperOk (some b2) v2 := by
                simpa [gamma] using h2
              have ha1 : a1.val ≤ v1.val := (lowerOk_some a1 v1).1 hg1.1
              have hb1 : v1.val ≤ b1.val := (upperOk_some b1 v1).1 hg1.2
              have ha2 : a2.val ≤ v2.val := (lowerOk_some a2 v2).1 hg2.1
              have hb2 : v2.val ≤ b2.val := (upperOk_some b2 v2).1 hg2.2
              simp only [leGuarded] at h
              split at h
              · rename_i hle
                cases h
                simp only [compare]
                exact decide_eq_true_eq.mpr (by omega)
              · split at h
                · rename_i hnle
                  cases h
                  simp only [compare]
                  exact decide_eq_false_iff_not.mpr (by omega)
                · simp at h

def cmpGuarded : CmpOp → Interval → Interval → Option Bool
  | .eq, a, b => eqGuarded a b
  | .ne, a, b => (eqGuarded a b).map Bool.not
  | .lt, a, b => ltGuarded a b
  | .le, a, b => leGuarded a b
  | .gt, a, b => ltGuarded b a
  | .ge, a, b => leGuarded b a

theorem compare_ne_eq_not (v1 v2 : I32) :
    compare .ne v1 v2 = !compare .eq v1 v2 := by
  by_cases h : v1.val = v2.val <;> simp [compare, h]

theorem cmpGuarded_sound {op : CmpOp} {a b : Interval} {r : Bool}
    (h : cmpGuarded op a b = some r) {v1 v2 : I32}
    (h1 : gamma a v1) (h2 : gamma b v2) :
    compare op v1 v2 = r := by
  cases op with
  | eq =>
      change eqGuarded a b = some r at h
      exact eqGuarded_sound h h1 h2
  | ne =>
      change (eqGuarded a b).map Bool.not = some r at h
      cases hE : eqGuarded a b with
      | none => simp [hE] at h
      | some x =>
          simp only [hE] at h
          cases h
          have hx := eqGuarded_sound hE h1 h2
          rw [compare_ne_eq_not, hx]
  | lt =>
      change ltGuarded a b = some r at h
      exact ltGuarded_sound h h1 h2
  | le =>
      change leGuarded a b = some r at h
      exact leGuarded_sound h h1 h2
  | gt =>
      change ltGuarded b a = some r at h
      have hg := ltGuarded_sound h h2 h1
      simpa [compare] using hg
  | ge =>
      change leGuarded b a = some r at h
      have hg := leGuarded_sound h h2 h1
      simpa [compare] using hg

/-- Three-valued abstract evaluation of a condition: `some true`/`some false`
only when every represented state evaluates to that value, `none` otherwise.
Strict in `and`/`or`, matching the concrete `evalB`. -/
def evalBGuarded (_lengths : Arr → Nat) (_vars : List Var) (_arrays : List Arr)
    (abs : Abs) : BExp → Option Bool
  | .cmp op l r =>
      evalExprGuarded _lengths _vars _arrays abs l >>= fun il =>
      evalExprGuarded _lengths _vars _arrays abs r >>= fun ir =>
        cmpGuarded op il ir
  | .not b => (evalBGuarded _lengths _vars _arrays abs b).map Bool.not
  | .and l r =>
      evalBGuarded _lengths _vars _arrays abs l >>= fun a =>
      evalBGuarded _lengths _vars _arrays abs r >>= fun b =>
        some (a && b)
  | .or l r =>
      evalBGuarded _lengths _vars _arrays abs l >>= fun a =>
      evalBGuarded _lengths _vars _arrays abs r >>= fun b =>
        some (a || b)

theorem evalBGuarded_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {b : BExp} {v : Bool}
    (h : evalBGuarded lengths vars arrays abs b = some v)
    (hs : GammaOn lengths vars arrays abs s) :
    evalB b s = some v := by
  induction b generalizing v with
  | cmp op l r =>
      simp only [evalBGuarded] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨il, hl, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨ir, hr, h3⟩
      rcases evalExprGuarded_sound hl hs with ⟨v1, he1, hg1⟩
      rcases evalExprGuarded_sound hr hs with ⟨v2, he2, hg2⟩
      have hcmp := cmpGuarded_sound h3 hg1 hg2
      simp only [evalB]
      rw [he1, he2]
      simp [hcmp]
  | not b ih =>
      simp only [evalBGuarded] at h
      cases hb : evalBGuarded lengths vars arrays abs b with
      | none => simp [hb] at h
      | some x =>
          simp only [hb] at h
          cases h
          have hbx := ih hb
          simp [evalB, hbx]
  | and l r ihl ihr =>
      simp only [evalBGuarded] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨a, ha, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨b, hb, h3⟩
      cases h3
      have ha' := ihl ha
      have hb' := ihr hb
      simp [evalB, ha', hb']
  | or l r ihl ihr =>
      simp only [evalBGuarded] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨a, ha, h2⟩
      rcases Option.bind_eq_some_iff.mp h2 with ⟨b, hb, h3⟩
      cases h3
      have ha' := ihl ha
      have hb' := ihr hb
      simp [evalB, ha', hb']

/-- The interval entailment test: `true` only when every represented state
evaluates the condition to `true`. -/
def entailsAbs (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr)
    (abs : Abs) (b : BExp) : Bool :=
  match evalBGuarded lengths vars arrays abs b with
  | some true => true
  | _ => false

theorem entailsAbs_sound {lengths : Arr → Nat} {vars : List Var}
    {arrays : List Arr} {abs : Abs} {s : State} {b : BExp}
    (h : entailsAbs lengths vars arrays abs b = true)
    (hs : GammaOn lengths vars arrays abs s) :
    evalB b s = some true := by
  unfold entailsAbs at h
  cases hb : evalBGuarded lengths vars arrays abs b with
  | none => simp [hb] at h
  | some v =>
      cases v with
      | false => simp [hb] at h
      | true => simpa [hb] using evalBGuarded_sound hb hs

/-! ### Initial state and `P` preservation -/

/-- The abstract state at a program's entry: supported variables and arrays are
zero (the concrete initial state is zero-initialised), everything else is `top`. -/
def initAbs (vars : List Var) (arrays : List Arr) : Abs :=
  { vars := fun x => if varMem x vars then toInterval I32.zero else top,
    mem := fun a => if arrMem a arrays then toInterval I32.zero else top }

/-- `initOf` is program-independent for intervals: the initial values are all
zero, and the array lengths are carried by `P`. -/
def initOf (vars : List Var) (arrays : List Arr) (_p : Program) : Abs :=
  initAbs vars arrays

theorem initOf_sound {lengths : Arr → Nat} {vars : List Var} {arrays : List Arr}
    (p : Program) (hP : POn lengths (State.init p)) :
    GammaOn lengths vars arrays (initOf vars arrays p) (State.init p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    cases hxm : varMem x vars with
    | false => simp [initOf, initAbs, hxm]
    | true => simp [initOf, initAbs, hxm, State.get, State.init, gamma_toInterval]
  · intro a ha
    exact hP a
  · intro a ha i hi
    cases ham : arrMem a arrays with
    | false => simp [initOf, initAbs, ham]
    | true =>
        simp only [initOf, initAbs, ham, ite_true]
        rw [State.memAt_init] at hi ⊢
        have hget : (Array.replicate (p.arrays.getD a 0) I32.zero).getD i I32.zero = I32.zero := by
          simp [Array.getD]
        rw [hget]
        exact gamma_toInterval I32.zero

/-- The canonical choice of `lengths` is the program's array table; then the
initial state satisfies `POn`, so `initOf_sound` gives the checker's base case. -/
theorem POn_init (p : Program) :
    POn (fun a => p.arrays.getD a 0) (State.init p) := by
  intro a
  rw [State.memAt_init]
  exact Array.size_replicate

theorem POn_step {lengths : Arr → Nat} {c : EdgeCmd} {s s' : State}
    (hP : POn lengths s) (h : EdgeCmd.exec c s = some s') :
    POn lengths s' := by
  intro arr
  cases c with
  | atomic cmd =>
      cases cmd with
      | skip =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          cases h
          exact hP arr
      | assign x e =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨v, he, hset⟩
          cases hset
          simpa [State.set, State.memAt] using hP arr
      | store a i e =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨idx, hi, h2⟩
          rcases Option.bind_eq_some_iff.mp h2 with ⟨val, hv, h3⟩
          split at h3
          · rename_i hbound
            cases h3
            by_cases hba : arr = a
            · subst arr
              have hsize : (Array.set (s.memAt a) idx.val.toNat val).size =
                  (s.memAt a).size := by
                apply Array.size_set
              rw [State.memAt_setMem_same]
              rw [hsize]
              exact hP a
            · rw [State.memAt_setMem_noteq s hba]
              exact hP arr
          · simp at h3
      | assert b =>
          simp only [EdgeCmd.exec, CFG.exec] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨v, hv, hif⟩
          split at hif
          · cases hif
            exact hP arr
          · simp at hif
  | assume b p =>
      cases p
      · simp only [EdgeCmd.exec] at h
        split at h
        · cases h
          exact hP arr
        · simp at h
      · simp only [EdgeCmd.exec] at h
        split at h
        · cases h
          exact hP arr
        · simp at h

/-- The interval `CertDomain` instance, parameterised by the program's declared
array lengths, variables and arrays. It supplies the checker's F1 fields
(`P_step`, `initOf`/`init_sound`, `entails`/`entails_sound`) in addition to the
M2 soundness fields. -/
def intervalDomain (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr) :
    CertDomain where
  P := POn lengths
  Abs := Abs
  gamma := GammaOn lengths vars arrays
  ble := bleAbs vars arrays
  ble_sound := by
    intro a b s h hP hg
    exact bleAbs_sound h hP hg
  top := topAbs
  top_sound := by
    intro s hP
    exact topAbs_sound hP
  transfer := transferAbs lengths vars arrays
  transfer_sound := by
    intro c a s s' hP hg h hP'
    exact transferAbs_sound hP hg h hP'
  join := joinAbs
  join_sound := by
    intro a b s hP h
    exact joinAbs_sound hP h
  P_step := by
    intro c s s' hP h
    exact POn_step hP h
  initOf := initOf vars arrays
  init_sound := by
    intro p hP
    exact initOf_sound p hP
  entails := entailsAbs lengths vars arrays
  entails_sound := by
    intro a b s h hP hg
    exact entailsAbs_sound h hg

end Interval
end CertCore

