import CertCore.I32

/-!
# `CertCore.Semantics` — trusted

Abstract syntax, configurations, the fuel-indexed deterministic small-step
semantics, and the safety predicate `Safe`.

Status: **syntax in progress — `Expr` done (M1.2); conditions and commands
pending (M1.3); semantics pending (M1.4–M1.7)**. This module is inside the TCB:
a bug here changes what "safe" means (plan §10.1).

Implemented (M1.2):

* `Var` — program variables are identified by name, matching the certificate
  format, whose abstract states are keyed by variable name.
* `Arr` — arrays are numbered, matching `State.mem : Nat → Array I32` (M1.4).
* `Expr` — constants, variable reads, `+ - * /`, array read, array length.

Pending:

* `BExp`, `Cmd`, `Program` (M1.3), including the condition language used by
  `if`, `while` and `assert`.
* `State`, `eval`, `step`, `run`, `Safe` (M1.4–M1.7).
* `edges` (M1.8), T1 `step_det` (M1.9), T2 `safe_iff` (M1.10).

Decisions that matter later:

* Constants are `I32`, not `Int`. An out-of-range source literal is therefore a
  *frontend* error (the parser uses `I32.ofInt?`), not a runtime `none`. The
  frontend is trusted anyway (D5); rejecting there is the right place, and it
  means every expression node is already in the machine range.
* Variables are strings and environments will be total functions
  `Var → I32` (M1.4), so evaluation cannot get stuck on a missing variable. The
  frontend rejects unbound names; the semantics stays total regardless.
* Division is an expression former, and its failure modes — zero divisor and the
  single overflow case `min / -1` — are fixed by `eval` in M1.5.
* Array reads carry an array number and an index expression; the array's length
  comes from the state, so `len` is total while `read` is partial (M1.5).
-/

namespace CertCore

/-- Program variables are identified by name.

The certificate format also keys abstract states by variable name
(`docs/certificate-v1.md`), so the AST needs no separate name-to-index table and
the checker can resolve a certificate directly against the program it parsed.
-/
abbrev Var : Type := String

/-- Arrays are numbered. `State.mem : Nat → Array I32` (M1.4) is indexed by this
number, matching the plan's state shape; the trusted frontend resolves source
array names to these indices. -/
abbrev Arr : Type := Nat

/-- Integer expressions of `Imp`.

Every former except `len` can fail during evaluation (M1.5):
`add`/`sub`/`mul` on signed overflow, `div` on a zero divisor or `min / -1`,
`read` on an out-of-bounds index. -/
inductive Expr : Type where
  /-- A source literal, already range-checked by the frontend. -/
  | const (n : I32)
  /-- A variable read. -/
  | var (x : Var)
  /-- Addition; overflows when the exact sum is outside the machine range. -/
  | add (l r : Expr)
  /-- Subtraction; overflows when the exact difference is outside the range. -/
  | sub (l r : Expr)
  /-- Multiplication; overflows when the exact product is outside the range. -/
  | mul (l r : Expr)
  /-- Truncating integer division; fails on a zero divisor and on `min / -1`. -/
  | div (l r : Expr)
  /-- Array read `a[i]`; fails when `i` is outside `[0, len(a))`. -/
  | read (a : Arr) (i : Expr)
  /-- Array length `len(a)`; total, since the state carries the array. -/
  | len (a : Arr)
  deriving DecidableEq, Repr

namespace Expr

/-- The zero constant, so expressions can be built in `Inhabited` contexts
(useful in tests and tooling; the semantics never needs a default). -/
instance : Inhabited Expr := ⟨.const I32.zero⟩

end Expr

end CertCore
