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
  .itv (some n) (some n) (by simp [loLeHi])

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
  simp [gamma, toInterval, lowerOk, upperOk]

/-- A singleton interval contains exactly its point. -/
theorem gamma_toInterval_iff {n v : I32} : gamma (toInterval n) v ↔ v = n := by
  constructor
  · intro h
    have h' : lowerOk (some n) v ∧ upperOk (some n) v := by
      simpa [gamma, toInterval] using h
    have h1 : n.val ≤ v.val := (lowerOk_some n v).1 h'.1
    have h2 : v.val ≤ n.val := (upperOk_some n v).1 h'.2
    exact I32.ext (by omega)
  · intro h
    subst v
    exact gamma_toInterval n

end Interval

end CertCore
