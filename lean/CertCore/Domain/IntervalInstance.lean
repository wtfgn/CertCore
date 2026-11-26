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

/-- Expression transfer restricted to the program support. Unknown variables
and arrays become `top`. -/
def evalExprAbsOn (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr)
    (abs : Abs) : Expr → Interval
  | .const n => toInterval n
  | .var x => if x ∈ vars then abs.vars x else top
  | .add l r => add (evalExprAbsOn lengths vars arrays abs l)
      (evalExprAbsOn lengths vars arrays abs r)
  | .sub l r => sub (evalExprAbsOn lengths vars arrays abs l)
      (evalExprAbsOn lengths vars arrays abs r)
  | .mul _ _ => top
  | .div _ _ => top
  | .read a _ => if a ∈ arrays then abs.mem a else top
  | .len a => if a ∈ arrays then lenInterval lengths a else top

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
      by_cases hx : x ∈ vars
      · simpa [evalExprAbsOn, hx] using hs.1 x hx
      · simp [evalExprAbsOn, hx]
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
  | div l r ihl ihr => simp [evalExprAbsOn]
  | read a i ihi =>
      simp only [eval] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨idx, hidx, hrest⟩
      by_cases ha : a ∈ arrays
      · split at hrest
        · rename_i hcond
          cases hrest
          have hnonneg : 0 ≤ idx.val := hcond.1
          have hlt : idx.val.toNat < (s.memAt a).size := by
            have hcast : (idx.val.toNat : Int) = idx.val := Int.toNat_of_nonneg hnonneg
            omega
          simpa [evalExprAbsOn, ha] using hs.2.2 a ha idx.val.toNat hlt
        · simp at hrest
      · simp [evalExprAbsOn, ha]
  | len a =>
      simp only [eval] at h
      by_cases ha : a ∈ arrays
      · have hlen : (s.memAt a).size = lengths a := hs.2.1 a ha
        rw [hlen] at h
        cases hof : I32.ofInt? (lengths a : Int) with
        | none => simp [hof] at h
        | some n =>
            have hn : n = v := by simpa [hof] using h
            subst n
            simp [evalExprAbsOn, ha, lenInterval, hof]
      · simp [evalExprAbsOn, ha]

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

/-! ## Edge transfer and the `CertDomain` instance -/

/-- Transfer a checker edge. Stores set the written array to `top`; guards and
asserts do not refine here (guard refinement is a later domain refinement). -/
def transferAbs (lengths : Arr → Nat) (vars : List Var) (arrays : List Arr) :
    EdgeCmd → Abs → Abs
  | .atomic .skip, abs => abs
  | .atomic (.assign x e), abs => assignAbsOn lengths vars arrays abs x e
  | .atomic (.store a _ e), abs => storeAbsOn lengths vars arrays abs a e
  | .atomic (.assert _), abs => abs
  | .assume _ _, abs => abs

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
        · cases h
          simpa [transferAbs] using hg
        · simp at h
      · simp only [EdgeCmd.exec] at h
        split at h
        · cases h
          simpa [transferAbs] using hg
        · simp at h

/-- The interval `CertDomain` instance, parameterised by the program's declared
array lengths, variables and arrays. -/
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

end Interval
end CertCore

