import CertCore.I32

/-!
# `CertCore.Semantics` — trusted

Abstract syntax, configurations, the fuel-indexed deterministic small-step
semantics, and the safety predicate `Safe`.

Status: **syntax complete (M1.2–M1.3); semantics pending (M1.4–M1.7)**. This
module is inside the TCB: a bug here changes what "safe" means (plan §10.1).

Implemented:

* `Var` — program variables by name, matching the certificate format's state keys.
* `Arr`, `Point` — arrays and program points by number, matching the plan's
  `State.mem : Nat → Array I32` and the certificate's point indices.
* `Expr` (M1.2) — constants, variable reads, `+ - * /`, array read, array length.
* `CmpOp`, `BExp` (M1.3) — comparisons and boolean connectives, the condition
  language for `if`, `while` and `assert`.
* `Cmd`, `Program` (M1.3) — `skip`, assignment, array store, `assert`, `if`,
  `while`, sequencing; atomic and branch commands carry their program point, and
  a `Program` carries the constant length of every array.

Pending:

* `State`, `eval`, `step`, `run`, `Safe` (M1.4–M1.7).
* `edges` (M1.8), T1 `step_det` (M1.9), T2 `safe_iff` (M1.10).

Decisions that matter later:

* Constants are `I32`, so an out-of-range source literal is a *frontend* error
  (the parser uses `I32.ofInt?`), not a runtime `none`; every expression node is
  already in the machine range.
* Variables are names and environments will be total `Var → I32` functions
  (M1.4), so evaluation cannot get stuck on a missing variable. The frontend
  rejects unbound names; the semantics stays total regardless.
* Division is an expression former (`Expr.div`), not a command. Its failure modes
  — zero divisor and `min / -1` — are fixed by `eval` in M1.5. A separate `div`
  command would duplicate `assign x (div l r)` and give the AST two encodings of
  one program, so it is deliberately not part of `Cmd`.
* Every command that *does* something at a point carries that point:
  `skip`, `assign`, `store`, `assert`, `if`, `while`. `seq` carries none; it is
  pure control. The entry point is derived (`Cmd.entry?`), not stored, so a
  program cannot disagree with itself about where it starts.
* **Semantics decision (reviewed at M1.3).** This is the structured *source* AST.
  The operational semantics will be **edge-based**: `edges : Program → List Edge`
  (M1.8, pulled forward to before `step`) compiles this AST to a CFG whose edges
  are the semantic steps, so T5 stays the plan's one-page induction over edge
  obligations. The alternative — structural big-step semantics plus a simulation
  lemma relating runs to edge obligations — was rejected because it moves proof
  work into the load-bearing theorem. The structured AST remains what the parser
  produces and what the Haskell mirror consumes; the certificate is about the
  compiled edges.
-/

namespace CertCore

/-- Program variables are identified by name.

The certificate format also keys abstract states by variable name
(`docs/certificate-v1.md`), so the AST needs no separate name-to-index table and
the checker can resolve a certificate directly against the program it parsed.
-/
abbrev Var : Type := String

/-- Arrays are numbered. `State.mem : Nat → Array I32` (M1.4) is indexed by this
number; `Program.arrays` fixes each array's constant length. -/
abbrev Arr : Type := Nat

/-- Program points are numbered. The trusted frontend assigns unique points; the
certificate's abstract states and the checker's obligations are indexed by them. -/
abbrev Point : Type := Nat

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

/-- Comparisons available in conditions. -/
inductive CmpOp : Type where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Boolean expressions: comparisons, negation, conjunction, disjunction.

Evaluation is total (M1.5): a comparison evaluates its two operands, and an
operand that fails makes the whole condition fail, so `if (10 / x > 0)` is a
division-by-zero obligation even though the comparison itself is total. -/
inductive BExp : Type where
  | cmp (op : CmpOp) (l r : Expr)
  | not (b : BExp)
  | and (l r : BExp)
  | or (l r : BExp)
  deriving DecidableEq, Repr

/-- Commands of `Imp`.

Atomic and branch commands carry the program point at which they execute; `seq`
is pure control and carries none. Division appears only inside `Expr`.
-/
inductive Cmd : Type where
  /-- Do nothing at point `p`. -/
  | skip (p : Point)
  /-- `x := e` at point `p`. -/
  | assign (p : Point) (x : Var) (e : Expr)
  /-- `a[i] := e` at point `p`; fails when `i` is out of bounds. -/
  | store (p : Point) (a : Arr) (i : Expr) (v : Expr)
  /-- `assert b` at point `p`; fails when `b` is false. -/
  | assert (p : Point) (b : BExp)
  /-- `if b then t else e` at branch point `p`. -/
  | ite (p : Point) (b : BExp) (t e : Cmd)
  /-- `while b do body` with the guard evaluated at point `p` on every iteration. -/
  | while (p : Point) (b : BExp) (body : Cmd)
  /-- Sequential composition; executes `first`, then `second`. -/
  | seq (first second : Cmd)
  deriving DecidableEq, Repr

namespace Cmd

/-- The first point executed by a command, if it executes at all.

Derived rather than stored: a `Program` cannot disagree with itself about where
execution starts. `seq` takes the first point of its first component. -/
def entry? : Cmd → Option Point
  | .skip p => some p
  | .assign p _ _ => some p
  | .store p _ _ _ => some p
  | .assert p _ => some p
  | .ite p _ _ _ => some p
  | .while p _ _ => some p
  | .seq first _ => entry? first

end Cmd

/-- A whole program: a command plus the constant length of every array.

`arrays[i]` is the length of array `i`; array numbers used by `Expr.read`,
`Expr.len` and `Cmd.store` must be in range (the trusted frontend guarantees it,
and the checker validates certificates against the same arrays).
-/
structure Program : Type where
  /-- The program body. -/
  body : Cmd
  /-- Constant array lengths, indexed by `Arr`. -/
  arrays : Array Nat
  deriving DecidableEq, Repr

namespace Program

/-- The program's entry point, derived from its body. -/
def entry? (program : Program) : Option Point := program.body.entry?

end Program

end CertCore
