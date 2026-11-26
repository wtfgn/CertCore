import CertCore.Semantics
import CertCore.Domain.Interval

/-!
# `CertCore.Domain.IntervalTransfer` — arithmetic transfer (M2.6)

The interval abstract state is `Env := Var → Interval`. Expression transfer is
`evalExpr : Env → Expr → Interval`; assignment updates one variable.

**Overflow policy (decided at M2.6):** if computing a finite endpoint leaves the
signed 32-bit range, the result collapses to `top`. The checker's safety
obligations separately rule out overflow on accepted executions. This keeps the
T4c proof simple and is a documented precision limitation.

Addition and subtraction are exact over the abstract bounds. Multiplication and
division currently collapse to `top`; refining them is a later precision
improvement, not a soundness requirement. Array reads and `len` are also `top`
until M2.7.
-/

namespace CertCore
namespace Interval

/-- The interval abstract state: one interval per source variable. -/
abbrev Env := Var → Interval

/-! ## Checked endpoint arithmetic -/

/-- Addition lower endpoint; `none` means overflow of the endpoint sum. -/
def addLower? : Option I32 → Option I32 → Option (Option I32)
  | none, _ => some none
  | _, none => some none
  | some a, some b => (I32.add? a b).map some

/-- Addition upper endpoint. -/
def addUpper? : Option I32 → Option I32 → Option (Option I32)
  | none, _ => some none
  | _, none => some none
  | some a, some b => (I32.add? a b).map some

/-- Subtraction lower endpoint `lo₁ - hi₂`. -/
def subLower? : Option I32 → Option I32 → Option (Option I32)
  | none, _ => some none
  | _, none => some none
  | some a, some b => (I32.sub? a b).map some

/-- Subtraction upper endpoint `hi₁ - lo₂`. -/
def subUpper? : Option I32 → Option I32 → Option (Option I32)
  | none, _ => some none
  | _, none => some none
  | some a, some b => (I32.sub? a b).map some

/-- Interval addition with the overflow-collapse policy. -/
def add : Interval → Interval → Interval
  | .bot, _ => .bot
  | _, .bot => .bot
  | .itv lo1 hi1 _, .itv lo2 hi2 _ =>
      match addLower? lo1 lo2, addUpper? hi1 hi2 with
      | some lo, some hi => ofBounds lo hi
      | _, _ => top

/-- Interval subtraction with the overflow-collapse policy. -/
def sub : Interval → Interval → Interval
  | .bot, _ => .bot
  | _, .bot => .bot
  | .itv lo1 hi1 _, .itv lo2 hi2 _ =>
      match subLower? lo1 hi2, subUpper? hi1 lo2 with
      | some lo, some hi => ofBounds lo hi
      | _, _ => top

/-- `gamma` of `ofBounds lo hi` follows from lower/upper facts about `v`. -/
theorem gamma_ofBounds_of_lower_upper {lo hi : Option I32} {v : I32}
    (hl : lowerOk lo v) (hu : upperOk hi v) : gamma (ofBounds lo hi) v := by
  cases lo with
  | none =>
      cases hi with
      | none => simp [ofBounds, ofBounds?, gamma, lowerOk, upperOk]
      | some b =>
          have hb : v.val ≤ b.val := (upperOk_some b v).1 hu
          have hof : ofBounds none (some b) = .itv none (some b) (by trivial) := rfl
          rw [hof]
          simp [gamma, lowerOk, upperOk, hb]
  | some a =>
      have ha : a.val ≤ v.val := (lowerOk_some a v).1 hl
      cases hi with
      | none =>
          have hof : ofBounds (some a) none = .itv (some a) none (by trivial) := rfl
          rw [hof]
          simp [gamma, lowerOk, upperOk, ha]
      | some b =>
          have hb : v.val ≤ b.val := (upperOk_some b v).1 hu
          have hab : a.val ≤ b.val := by omega
          rw [ofBounds_of_le hab]
          simp [gamma, lowerOk_some, upperOk_some, ha, hb]

/-! ## Endpoint soundness -/

theorem addLower?_sound {lo1 lo2 : Option I32} {v1 v2 v : I32}
    (h1 : lowerOk lo1 v1) (h2 : lowerOk lo2 v2)
    (hv : v.val = v1.val + v2.val) {lo : Option I32}
    (h : addLower? lo1 lo2 = some lo) : lowerOk lo v := by
  cases lo1 with
  | none =>
      have hnone : lo = none := by simpa [addLower?] using h.symm
      subst lo
      exact lowerOk_none v
  | some a =>
      cases lo2 with
      | none =>
          have hnone : lo = none := by simpa [addLower?] using h.symm
          subst lo
          exact lowerOk_none v
      | some b =>
          rcases Option.map_eq_some_iff.mp (by simpa [addLower?] using h) with
            ⟨c, hc, rfl⟩
          have hc' : c.val = a.val + b.val := I32.add?_sound hc
          have ha : a.val ≤ v1.val := (lowerOk_some a v1).1 h1
          have hb : b.val ≤ v2.val := (lowerOk_some b v2).1 h2
          exact (lowerOk_some c v).2 (by omega)

theorem addUpper?_sound {hi1 hi2 : Option I32} {v1 v2 v : I32}
    (h1 : upperOk hi1 v1) (h2 : upperOk hi2 v2)
    (hv : v.val = v1.val + v2.val) {hi : Option I32}
    (h : addUpper? hi1 hi2 = some hi) : upperOk hi v := by
  cases hi1 with
  | none =>
      have hnone : hi = none := by simpa [addUpper?] using h.symm
      subst hi
      exact upperOk_none v
  | some a =>
      cases hi2 with
      | none =>
          have hnone : hi = none := by simpa [addUpper?] using h.symm
          subst hi
          exact upperOk_none v
      | some b =>
          rcases Option.map_eq_some_iff.mp (by simpa [addUpper?] using h) with
            ⟨c, hc, rfl⟩
          have hc' : c.val = a.val + b.val := I32.add?_sound hc
          have ha : v1.val ≤ a.val := (upperOk_some a v1).1 h1
          have hb : v2.val ≤ b.val := (upperOk_some b v2).1 h2
          exact (upperOk_some c v).2 (by omega)

theorem subLower?_sound {lo1 hi2 : Option I32} {v1 v2 v : I32}
    (h1 : lowerOk lo1 v1) (h2 : upperOk hi2 v2)
    (hv : v.val = v1.val - v2.val) {lo : Option I32}
    (h : subLower? lo1 hi2 = some lo) : lowerOk lo v := by
  cases lo1 with
  | none =>
      have hnone : lo = none := by simpa [subLower?] using h.symm
      subst lo
      exact lowerOk_none v
  | some a =>
      cases hi2 with
      | none =>
          have hnone : lo = none := by simpa [subLower?] using h.symm
          subst lo
          exact lowerOk_none v
      | some b =>
          rcases Option.map_eq_some_iff.mp (by simpa [subLower?] using h) with
            ⟨c, hc, rfl⟩
          have hc' : c.val = a.val - b.val := I32.sub?_sound hc
          have ha : a.val ≤ v1.val := (lowerOk_some a v1).1 h1
          have hb : v2.val ≤ b.val := (upperOk_some b v2).1 h2
          exact (lowerOk_some c v).2 (by omega)

theorem subUpper?_sound {hi1 lo2 : Option I32} {v1 v2 v : I32}
    (h1 : upperOk hi1 v1) (h2 : lowerOk lo2 v2)
    (hv : v.val = v1.val - v2.val) {hi : Option I32}
    (h : subUpper? hi1 lo2 = some hi) : upperOk hi v := by
  cases hi1 with
  | none =>
      have hnone : hi = none := by simpa [subUpper?] using h.symm
      subst hi
      exact upperOk_none v
  | some a =>
      cases lo2 with
      | none =>
          have hnone : hi = none := by simpa [subUpper?] using h.symm
          subst hi
          exact upperOk_none v
      | some b =>
          rcases Option.map_eq_some_iff.mp (by simpa [subUpper?] using h) with
            ⟨c, hc, rfl⟩
          have hc' : c.val = a.val - b.val := I32.sub?_sound hc
          have ha : v1.val ≤ a.val := (upperOk_some a v1).1 h1
          have hb : b.val ≤ v2.val := (lowerOk_some b v2).1 h2
          exact (upperOk_some c v).2 (by omega)

/-! ## T4c for expressions -/

theorem add_sound {a b : Interval} {v1 v2 v : I32}
    (ha : gamma a v1) (hb : gamma b v2) (h : I32.add? v1 v2 = some v) :
    gamma (add a b) v := by
  cases a with
  | bot => simp [gamma] at ha
  | itv lo1 hi1 w1 =>
      cases b with
      | bot => simp [gamma] at hb
      | itv lo2 hi2 w2 =>
          have h1 : lowerOk lo1 v1 ∧ upperOk hi1 v1 := by simpa [gamma] using ha
          have h2 : lowerOk lo2 v2 ∧ upperOk hi2 v2 := by simpa [gamma] using hb
          have hv : v.val = v1.val + v2.val := I32.add?_sound h
          cases hL : addLower? lo1 lo2 with
          | none =>
              simp [add, hL]
          | some lo =>
              cases hU : addUpper? hi1 hi2 with
              | none => simp [add, hL, hU]
              | some hi =>
                  have hl : lowerOk lo v := addLower?_sound h1.1 h2.1 hv hL
                  have hu : upperOk hi v := addUpper?_sound h1.2 h2.2 hv hU
                  simpa [add, hL, hU] using gamma_ofBounds_of_lower_upper hl hu

theorem sub_sound {a b : Interval} {v1 v2 v : I32}
    (ha : gamma a v1) (hb : gamma b v2) (h : I32.sub? v1 v2 = some v) :
    gamma (sub a b) v := by
  cases a with
  | bot => simp [gamma] at ha
  | itv lo1 hi1 w1 =>
      cases b with
      | bot => simp [gamma] at hb
      | itv lo2 hi2 w2 =>
          have h1 : lowerOk lo1 v1 ∧ upperOk hi1 v1 := by simpa [gamma] using ha
          have h2 : lowerOk lo2 v2 ∧ upperOk hi2 v2 := by simpa [gamma] using hb
          have hv : v.val = v1.val - v2.val := I32.sub?_sound h
          cases hL : subLower? lo1 hi2 with
          | none =>
              simp [sub, hL]
          | some lo =>
              cases hU : subUpper? hi1 lo2 with
              | none => simp [sub, hL, hU]
              | some hi =>
                  have hl : lowerOk lo v := subLower?_sound h1.1 h2.2 hv hL
                  have hu : upperOk hi v := subUpper?_sound h1.2 h2.1 hv hU
                  simpa [sub, hL, hU] using gamma_ofBounds_of_lower_upper hl hu

/-- Expression transfer. Multiplication, division, array read and `len` are
currently `top` (see the module note); the other arithmetic is precise. -/
def evalExpr (env : Env) : Expr → Interval
  | .const n => toInterval n
  | .var x => env x
  | .add l r => add (evalExpr env l) (evalExpr env r)
  | .sub l r => sub (evalExpr env l) (evalExpr env r)
  | .mul _ _ => top
  | .div _ _ => top
  | .read _ _ => top
  | .len _ => top

/-- Assignment updates the abstract environment at one variable. -/
def assign (env : Env) (x : Var) (e : Expr) : Env :=
  funUpdate env x (evalExpr env e)

/-- **T4c (expressions):** `evalExpr` is sound for successful evaluation. -/
theorem evalExpr_sound {env : Env} {s : State} {e : Expr} {v : I32}
    (hstate : ∀ x, gamma (env x) (s.get x)) (h : eval e s = some v) :
    gamma (evalExpr env e) v := by
  induction e generalizing v with
  | const n =>
      simp only [eval] at h
      cases h
      simp [evalExpr]
  | var x =>
      simp only [eval] at h
      cases h
      simpa [evalExpr] using hstate x
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
      simp [evalExpr]
  | div l r ihl ihr =>
      simp [evalExpr]
  | read a i ihi =>
      simp [evalExpr]
  | len a =>
      simp [evalExpr]

/-- **T4c (assignment):** assigning the transferred expression keeps the
abstract state sound. -/
theorem assign_sound {env : Env} {s : State} {x : Var} {e : Expr} {v : I32}
    (hstate : ∀ y, gamma (env y) (s.get y))
    (h : eval e s = some v) :
    ∀ y, gamma (assign env x e y) ((s.set x v).get y) := by
  intro y
  by_cases hy : y = x
  · subst y
    have he := evalExpr_sound hstate h
    simpa [assign, State.set, State.get, funUpdate] using he
  · simpa [assign, State.set, State.get, funUpdate, hy] using hstate y

end Interval
end CertCore
