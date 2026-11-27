import CertCore.I32

/-!
# `CertCore.Domain.Interval` — the interval domain's value type (M2.1)

An interval over signed 32-bit integers:

* `bot` is the empty set;
* `itv lo hi` has an optional lower and upper bound, where `none` means
  unbounded on that side, and carries a proof that finite bounds are ordered.
  The proof makes an inverted interval (`lo > hi`) unrepresentable, so there is
  exactly one representation of the empty set (`bot`).
* `Interval.ofBounds` is the normalising smart constructor for internal use: it
  returns `bot` for inverted bounds.
* `Interval.ofBounds?` is the **checked** constructor for the frontend and the
  certificate decoder: inverted finite bounds are `none`, so the decoder can
  report `Diagnostic.malformed` instead of silently producing `bot`.
* `Interval.toInterval` is the singleton injection used by constants.

`⊤` is `itv none none`; it is introduced with the other domain operations at
M2.5 rather than as a special constructor here.

The gamma function, inclusion, join and transfer are M2.2–M2.6 and live in this
file as they land.
-/

namespace CertCore

/-- Bound order for interval endpoints: `none` is unbounded, so it is below
every lower bound and above every upper bound. For finite bounds, compare values. -/
def loLeHi : Option I32 → Option I32 → Prop
  | some a, some b => a.val ≤ b.val
  | _, _ => True

instance : ∀ lo hi : Option I32, Decidable (loLeHi lo hi)
  | some a, some b => inferInstanceAs (Decidable (a.val ≤ b.val))
  | none, _ => isTrue trivial
  | some _, none => isTrue trivial

/-- An interval with an explicit empty case.

The `valid` proof prevents constructing an inverted interval, so `bot` is the
only representation of the empty set and certificate bytes have a single
canonical encoding. -/
inductive Interval : Type where
  /-- The empty interval. -/
  | bot
  /-- A non-empty description: optionally bounded on each side. -/
  | itv (lo : Option I32) (hi : Option I32) (valid : loLeHi lo hi)
  deriving DecidableEq, Repr

namespace Interval

instance : Inhabited Interval := ⟨bot⟩

/-- The singleton interval `[n, n]`. Used for source constants. -/
def toInterval (n : I32) : Interval :=
  .itv (some n) (some n) (by exact Int.le_refl n.val)

/-- Checked constructor: `none` exactly when both bounds are finite and inverted.

This is the constructor the frontend and the certificate decoder use: a
certificate with `lo > hi` must become `Diagnostic.malformed` (T10), not `bot`.
`ofBounds` is the normalising variant for internal use. -/
def ofBounds? : Option I32 → Option I32 → Option Interval
  | some a, some b =>
      if h : a.val ≤ b.val then some (.itv (some a) (some b) h) else none
  | none, hi => some (.itv none hi (by trivial))
  | some a, none => some (.itv (some a) none (by trivial))

/-- Smart constructor for internal use: inverted finite bounds become `bot`;
unbounded sides are `none`. This is a *normalising* constructor — it must not be
used on certificate input, where inverted bounds are malformed. -/
def ofBounds (lo hi : Option I32) : Interval :=
  (ofBounds? lo hi).getD .bot

@[simp] theorem ofBounds?_bot_of_not_le {a b : I32} (h : ¬ a.val ≤ b.val) :
    ofBounds? (some a) (some b) = none := by
  simp [ofBounds?, h]

@[simp] theorem ofBounds?_of_le {a b : I32} (h : a.val ≤ b.val) :
    ofBounds? (some a) (some b) =
      some (.itv (some a) (some b) (by simpa [loLeHi] using h)) := by
  simp [ofBounds?, h]

@[simp] theorem ofBounds?_none_none :
    ofBounds? none none = some (.itv none none (by trivial)) := rfl

@[simp] theorem ofBounds_bot_of_not_le {a b : I32} (h : ¬ a.val ≤ b.val) :
    ofBounds (some a) (some b) = .bot := by
  simp [ofBounds, ofBounds?, h]

@[simp] theorem ofBounds_of_le {a b : I32} (h : a.val ≤ b.val) :
    ofBounds (some a) (some b) =
      .itv (some a) (some b) (by simpa [loLeHi] using h) := by
  simp [ofBounds, ofBounds?, h]

@[simp] theorem ofBounds_none_none : ofBounds none none = .itv none none (by trivial) := rfl

/-! ## Membership (M2.2)

Lean core (without Mathlib) has no `Set`, so `gamma` is a predicate
`Interval → I32 → Prop`; `gamma i v` is the plan's `v ∈ γ i`.
-/

/-- The lower-bound half of membership: every finite lower bound is below `v`. -/
def lowerOk (lo : Option I32) (v : I32) : Prop :=
  ∀ a, lo = some a → a.val ≤ v.val

/-- The upper-bound half of membership: every finite upper bound is above `v`. -/
def upperOk (hi : Option I32) (v : I32) : Prop :=
  ∀ b, hi = some b → v.val ≤ b.val

@[simp] theorem lowerOk_none (v : I32) : lowerOk none v := by
  intro a h
  cases h

@[simp] theorem lowerOk_some (a v : I32) : lowerOk (some a) v ↔ a.val ≤ v.val := by
  constructor
  · intro h
    exact h a rfl
  · intro h b hb
    cases hb
    exact h

@[simp] theorem upperOk_none (v : I32) : upperOk none v := by
  intro b h
  cases h

@[simp] theorem upperOk_some (a v : I32) : upperOk (some a) v ↔ v.val ≤ a.val := by
  constructor
  · intro h
    exact h a rfl
  · intro h b hb
    cases hb
    exact h

/-- Concrete membership in an interval. `bot` is empty; an `itv` contains exactly
the values between its finite bounds. -/
def gamma (i : Interval) (v : I32) : Prop :=
  match i with
  | .bot => False
  | .itv lo hi _ => lowerOk lo v ∧ upperOk hi v

@[simp] theorem gamma_bot (v : I32) : ¬ gamma .bot v := by
  simp [gamma]

@[simp] theorem gamma_itv (lo hi : Option I32) (valid : loLeHi lo hi) (v : I32) :
    gamma (.itv lo hi valid) v ↔ lowerOk lo v ∧ upperOk hi v := Iff.rfl

@[simp] theorem gamma_toInterval (n : I32) : gamma (toInterval n) n := by
  constructor
  · intro a h
    cases h
    exact Int.le_refl n.val
  · intro a h
    cases h
    exact Int.le_refl n.val

/-- A singleton interval contains exactly its point. -/
theorem gamma_toInterval_iff {n v : I32} : gamma (toInterval n) v ↔ v = n := by
  constructor
  · intro h
    have h' : lowerOk (some n) v ∧ upperOk (some n) v := by
      change lowerOk (some n) v ∧ upperOk (some n) v at h
      exact h
    have h1 : n.val ≤ v.val := (lowerOk_some n v).1 h'.1
    have h2 : v.val ≤ n.val := (upperOk_some n v).1 h'.2
    exact I32.ext (by omega)
  · intro h
    subst v
    exact gamma_toInterval n

/-! ## Inclusion (M2.3)

`ble a b` decides `γ a ⊆ γ b`. The two endpoint orders differ at `none`:
`none` is `-∞` on the lower side and `+∞` on the upper side.
-/

/-- Lower-bound order: `none` is `-∞`. -/
def leLo : Option I32 → Option I32 → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => a.val ≤ b.val

/-- Upper-bound order: `none` is `+∞`. -/
def leHi : Option I32 → Option I32 → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => true
  | some a, some b => a.val ≤ b.val

/-- Inclusion `γ a ⊆ γ b`.

An interval is included in another when the right-hand lower bound is weaker
(`lo₂ ≤ lo₁`) and the right-hand upper bound is weaker (`hi₁ ≤ hi₂`); `bot` is
included in everything. This is a decision procedure, not a proof: `ble_sound`
is M2.4. -/
def ble : Interval → Interval → Bool
  | .bot, .bot => true
  | .bot, .itv _ _ _ => true
  | .itv _ _ _, .bot => false
  | .itv lo1 hi1 _, .itv lo2 hi2 _ => leLo lo2 lo1 && leHi hi1 hi2

/-- `leLo lo2 lo1` is the endpoint fact needed for inclusion: a weaker lower
bound on the right keeps every value of the left interval. -/
theorem leLo_sound {lo1 lo2 : Option I32} (h : leLo lo2 lo1 = true) :
    ∀ v, lowerOk lo1 v → lowerOk lo2 v := by
  intro v hv
  cases lo1 with
  | none =>
      cases lo2 with
      | none => exact lowerOk_none v
      | some a2 => simp [leLo] at h
  | some a1 =>
      cases lo2 with
      | none => exact lowerOk_none v
      | some a2 =>
          simp [leLo] at h
          have ha1 : a1.val ≤ v.val := (lowerOk_some a1 v).1 hv
          exact (lowerOk_some a2 v).2 (by omega)

/-- `leHi hi1 hi2` is the endpoint fact needed for inclusion: a weaker upper
bound on the right keeps every value of the left interval. -/
theorem leHi_sound {hi1 hi2 : Option I32} (h : leHi hi1 hi2 = true) :
    ∀ v, upperOk hi1 v → upperOk hi2 v := by
  intro v hv
  cases hi1 with
  | none =>
      cases hi2 with
      | none => exact upperOk_none v
      | some a2 => simp [leHi] at h
  | some a1 =>
      cases hi2 with
      | none => exact upperOk_none v
      | some a2 =>
          simp [leHi] at h
          have ha1 : v.val ≤ a1.val := (upperOk_some a1 v).1 hv
          exact (upperOk_some a2 v).2 (by omega)

/-- **T4 (inclusion):** `ble` is sound for `gamma`. -/
theorem ble_sound {a b : Interval} (h : ble a b = true) :
    ∀ v, gamma a v → gamma b v := by
  intro v hv
  cases a with
  | bot =>
      simp [gamma] at hv
  | itv lo1 hi1 w1 =>
      cases b with
      | bot =>
          simp [ble] at h
      | itv lo2 hi2 w2 =>
          have h' : leLo lo2 lo1 = true ∧ leHi hi1 hi2 = true := by
            simpa [ble] using h
          have hv' : lowerOk lo1 v ∧ upperOk hi1 v := by
            simpa [gamma] using hv
          have hl : lowerOk lo2 v := leLo_sound h'.1 v hv'.1
          have hu : upperOk hi2 v := leHi_sound h'.2 v hv'.2
          simpa [gamma] using And.intro hl hu

/-! ## Join (M2.4)

The join is the convex hull: the weaker of the two lower bounds and the stronger
of the two upper bounds. An unbounded side absorbs the other side.
-/

/-- The weaker lower bound: `none` (`-∞`) absorbs anything. -/
def minLo : Option I32 → Option I32 → Option I32
  | none, _ => none
  | some _, none => none
  | some a, some b => if a.val ≤ b.val then some a else some b

/-- The stronger upper bound: `none` (`+∞`) absorbs anything. -/
def maxHi : Option I32 → Option I32 → Option I32
  | none, _ => none
  | some _, none => none
  | some a, some b => if a.val ≤ b.val then some b else some a

/-- The convex hull's bounds are ordered whenever the inputs are. -/
theorem loLeHi_min_max {lo1 hi1 lo2 hi2 : Option I32}
    (w1 : loLeHi lo1 hi1) (w2 : loLeHi lo2 hi2) :
    loLeHi (minLo lo1 lo2) (maxHi hi1 hi2) := by
  cases lo1 with
  | none => cases hi1 <;> cases lo2 <;> cases hi2 <;> simp [minLo, maxHi, loLeHi]
  | some a1 =>
    cases hi1 with
    | none => cases lo2 <;> cases hi2 <;> simp [minLo, maxHi, loLeHi]
    | some b1 =>
      cases lo2 with
      | none => cases hi2 <;> simp [minLo, maxHi, loLeHi]
      | some a2 =>
        cases hi2 with
        | none => simp [minLo, maxHi, loLeHi]
        | some b2 =>
          simp only [loLeHi] at w1 w2
          dsimp [minLo, maxHi]
          by_cases hmin : a1.val ≤ a2.val
          · by_cases hmax : b1.val ≤ b2.val
            · simp [loLeHi, hmin, hmax]; omega
            · simp [loLeHi, hmin, hmax]; omega
          · by_cases hmax : b1.val ≤ b2.val
            · simp [loLeHi, hmin, hmax]; omega
            · simp [loLeHi, hmin, hmax]; omega

/-- `minLo` is below its left argument. -/
theorem leLo_minLo_left (lo1 lo2 : Option I32) :
    leLo (minLo lo1 lo2) lo1 = true := by
  cases lo1 with
  | none => cases lo2 <;> rfl
  | some a =>
      cases lo2 with
      | none => rfl
      | some b =>
          dsimp only [minLo]
          split
          · simp only [leLo, decide_eq_true_eq]
            omega
          · simp only [leLo, decide_eq_true_eq]
            omega

/-- `minLo` is below its right argument. -/
theorem leLo_minLo_right (lo1 lo2 : Option I32) :
    leLo (minLo lo1 lo2) lo2 = true := by
  cases lo1 with
  | none => cases lo2 <;> rfl
  | some a =>
      cases lo2 with
      | none => rfl
      | some b =>
          dsimp only [minLo]
          split
          · simp only [leLo, decide_eq_true_eq]
            omega
          · simp only [leLo, decide_eq_true_eq]
            omega

/-- `maxHi` is above its left argument. -/
theorem leHi_maxHi_left (hi1 hi2 : Option I32) :
    leHi hi1 (maxHi hi1 hi2) = true := by
  cases hi1 with
  | none => cases hi2 <;> rfl
  | some a =>
      cases hi2 with
      | none => rfl
      | some b =>
          dsimp only [maxHi]
          split
          · simp only [leHi, decide_eq_true_eq]
            omega
          · simp only [leHi, decide_eq_true_eq]
            omega

/-- `maxHi` is above its right argument. -/
theorem leHi_maxHi_right (hi1 hi2 : Option I32) :
    leHi hi2 (maxHi hi1 hi2) = true := by
  cases hi1 with
  | none => cases hi2 <;> rfl
  | some a =>
      cases hi2 with
      | none => rfl
      | some b =>
          dsimp only [maxHi]
          split
          · simp only [leHi, decide_eq_true_eq]
            omega
          · simp only [leHi, decide_eq_true_eq]
            omega

/-- Convex-hull join. `bot` is the identity. -/
def join : Interval → Interval → Interval
  | .bot, i => i
  | i, .bot => i
  | .itv lo1 hi1 w1, .itv lo2 hi2 w2 =>
      .itv (minLo lo1 lo2) (maxHi hi1 hi2) (loLeHi_min_max w1 w2)

/-- **T4b (join):** the convex hull contains both operands. -/
theorem join_sound {a b : Interval} {v : I32}
    (h : gamma a v ∨ gamma b v) : gamma (join a b) v := by
  cases a with
  | bot =>
      cases b with
      | bot => simp [gamma] at h
      | itv lo2 hi2 w2 =>
          rcases h with h | h
          · simp [gamma] at h
          · simpa [join] using h
  | itv lo1 hi1 w1 =>
      cases b with
      | bot =>
          rcases h with h | h
          · simpa [join] using h
          · simp [gamma] at h
      | itv lo2 hi2 w2 =>
          rcases h with h | h
          · have hv : lowerOk lo1 v ∧ upperOk hi1 v := by
              simpa [gamma] using h
            have hl : lowerOk (minLo lo1 lo2) v :=
              leLo_sound (leLo_minLo_left lo1 lo2) v hv.1
            have hu : upperOk (maxHi hi1 hi2) v :=
              leHi_sound (leHi_maxHi_left hi1 hi2) v hv.2
            simpa [join, gamma] using And.intro hl hu
          · have hv : lowerOk lo2 v ∧ upperOk hi2 v := by
              simpa [gamma] using h
            have hl : lowerOk (minLo lo1 lo2) v :=
              leLo_sound (leLo_minLo_right lo1 lo2) v hv.1
            have hu : upperOk (maxHi hi1 hi2) v :=
              leHi_sound (leHi_maxHi_right hi1 hi2) v hv.2
            simpa [join, gamma] using And.intro hl hu

/-! ## Top (M2.5) -/

/-- The top element: no information, i.e. every value. -/
def top : Interval := .itv none none (by trivial)

/-- **T4 (top):** every value is in `top`. -/
@[simp] theorem top_sound (v : I32) : gamma top v := by
  simp [top, gamma, lowerOk, upperOk]

end Interval

end CertCore
