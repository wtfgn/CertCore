import CertCore.I32

/-!
# `CertCore.Semantics` — trusted

Abstract syntax, configurations, the fuel-indexed deterministic small-step
semantics, and the safety predicate `Safe`.

Status: **M1 complete.** Syntax, state, evaluation, the compiled CFG, `step`,
`run`/`Safe`, the edge projection, the three example fixtures, T1 `step_det`
(M1.9), T2 `safe_iff` (M1.10), and the well-formedness/bridge lemmas
`Program.compile_wf` and `CFG.step_edge`. There is no parser, certificate decoder,
domain instance, or checker yet; those are M2–M4. This module is inside the TCB:
a bug here changes what "safe" means (plan §10.1).

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
* `State` (M1.4) — a total environment `Var → I32` and total memory
  `Arr → Array I32`, with initialisation and pointwise update lemmas.
* `eval`, `evalB` (M1.5) — expression and condition evaluation to `Option`;
  `none` for division by zero, `min / -1`, signed overflow and out-of-bounds
  read. This is where the safety property is defined.
* `AtomicCmd`, `Instr`, `CFG`, `Cmd.compile`, `Program.compile`, `CFG.step`
  (M1.6) — the compiled edge machine: one instruction per step, deterministic
  branches, a halt point that stutters, and `none` reserved for the hazards.
* `CFG.run`, `CFG.Safe`, `Program.safe` (M1.7) — fuel-indexed iteration of `step`;
  `Safe` quantifies over every finite number of steps, so diverging runs and the
  halt stutter are safe and fuel exhaustion is not failure.
* `EdgeCmd`, `Edge`, `Instr.edgesAt`, `CFG.edges` (M1.8) — the checker-facing
  projection: atomic edges plus `assume` edges carrying a branch's guard
  polarity, in ascending point order, with membership lemmas for the kernel proof.
* `Instr.targetsLt`, `CFG.WF`, `Program.compile_wf` — every compiled CFG has an
  in-range entry and every instruction successor is inside the instruction array.
* `Cmd.points`, `Program.checkWF`, `Program.compileChecked` — the decidable
  source contract (unique points, declared arrays within resource bounds,
  assigned reads, bounded `maxPoint`) and the fail-closed compilation entry point.
* `EdgeCmd.exec`, `CFG.step_edge` — the effect of a checker edge, and the proof
  that every successful `step` is one edge of the graph.
* `CFG.step_det` (T1, M1.9) and `CFG.safe_iff` / `safe_iff_exists` (T2, M1.10).
* The three `.imp` fixtures (M1.11), hand-encoded in `Tests/Examples.lean`.

Not in M1:

* M2: `CertDomain` and the interval instance.
* M3: `check`, the three obligation families, and T5.
* M4: the parser, the total decoder, and `certcore check`.

Decisions that matter later:

* **Fuel exhaustion is not failure.** `run 0` returns the starting
  configuration, and `none` appears only when a step fails. `Safe` is
  `∀ n, run n entry s ≠ none`, so a diverging run (including the halt stutter)
  is safe: every finite prefix is. This is the plan's D6 choice, now realised
  over the compiled machine.
* **`Program.safe` requires `Program.WF`** and pairs the compiled machine with
  `State.init`, so the program-level theorem (T5) is about a well-formed program's
  initial state; the state-general `CFG.Safe` stays available for the trace
  lemmas.

* **Edges are recomputed, never supplied.** `CFG.edges` is the checker's view of
  the compiled graph: the analyzer's certificate carries states, not edges, so a
  hostile certificate cannot invent a successor set. Branch guards become
  `assume b true` / `assume b false` edges, which is also where the domain's
  guard refinement will attach (M2.6).
* **One branch is one step, two edges.** `CFG.step` evaluates the condition and
  moves to one side; the projection then contains both possible edges, and the
  checker must discharge an obligation for each. The two views agree by
  `mem_edges_branch_true` / `mem_edges_branch_false`; `CFG.step_edge` packages
  the bridge for T5.

* Constants are `I32`, so an out-of-range source literal is a *frontend* error
  (the parser uses `I32.ofInt?`), not a runtime `none`; every expression node is
  already in the machine range.
* Variables are names and environments are total `Var → I32` functions (M1.4),
  so evaluation cannot get stuck on a missing variable. The frontend rejects
  unbound names; the semantics stays total regardless.
* Division is an expression former (`Expr.div`), not a command. Its failure modes
  — zero divisor and `min / -1` — are fixed by `eval` in M1.5. A separate `div`
  command would duplicate `assign x (div l r)` and give the AST two encodings of
  one program, so it is deliberately not part of `Cmd`.
* **Division truncates toward zero** (`Int.tdiv`), matching C-family machine
  arithmetic and x86 `idiv`. Lean's `Int` division is Euclidean (`-7 / 2 = -4`),
  so it is deliberately not used; the evaluation tests pin `(-7) / 2 = -3`.
  `min / -1` is an overflow and yields `none`. Division has no wrapping
  counterpart: a machine divide overflow traps.
* **Conditions are strict.** `BExp.and` and `BExp.or` evaluate both operands.
  A short-circuit language would make a partial operation on the right a
  *conditional* safety obligation ("only if the left is true"), which the
  checker's per-point safety predicates do not express; strictness keeps every
  obligation unconditional. This differs from C's `&&`/`||` and is revisited
  only if the language should match C.
* Every command that *does* something at a point carries that point:
  `skip`, `assign`, `store`, `assert`, `if`, `while`. `seq` carries none; it is
  pure control. The entry point is derived (`Cmd.entry`), not stored, so a
  program cannot disagree with itself about where it starts.
* **Semantics decision (reviewed at M1.3, realised at M1.6).** This is the
  structured *source* AST; the operational semantics is **edge-based**.
  `Cmd.compile`/`Program.compile` (M1.6) lower the AST to a `CFG` of instructions
  (atomic actions and deterministic branches), and `CFG.step` walks one
  instruction at a time. The checker-facing `Edge = Point × EdgeCmd × Point`
  projection is M1.8. This keeps T5 the plan's one-page induction over edge
  obligations; the structural alternative — big-step semantics plus a simulation
  lemma relating runs to edges — was rejected because it moves proof work into
  the load-bearing theorem. The structured AST remains what the parser produces
  and what the Haskell mirror consumes; the certificate is about the compiled
  graph.
* **The compiler is trusted.** `Cmd.compile` is small, deterministic and in the
  TCB; a bug there changes what the program means. Every write goes through
  `place`, whose in-range proof is an argument: an out-of-range write is not a
  representable call, so the compiler cannot silently drop an instruction.
  `Program.compile_wf` proves that every compiled CFG has an in-range entry and
  successors. `Program.checkWF` rejects duplicate points, undeclared array
  indices, unassigned reads, and an oversized `maxPoint`; `compileChecked`
  returns `none` for those programs. The Haskell mirror will have to agree with
  the compiler.
* **Halting is a stutter.** Compilation adds a halt point holding `skip` to
  itself, so termination is never `none`. `none` is reserved for the four hazards
  (plus an out-of-range point, which is a malformed CFG rather than a
  language-level failure).
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
  /-- Array length `len(a)`; the state carries the array, so it never fails for a
  missing array. It can only fail if the length exceeds the machine range, which
  the frontend's constant bounds exclude. -/
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

/-- The first point executed by a command.

Derived rather than stored: a `Program` cannot disagree with itself about where
execution starts. `seq` takes the first point of its first component. -/
def entry : Cmd → Point
  | .skip p => p
  | .assign p _ _ => p
  | .store p _ _ _ => p
  | .assert p _ => p
  | .ite p _ _ _ => p
  | .while p _ _ => p
  | .seq first _ => entry first

end Cmd

namespace Expr

/-- Array indices mentioned by an expression. Used by `Program.WF` to check that
the program only refers to declared arrays. -/
def arrs : Expr → List Arr
  | .const _ => []
  | .var _ => []
  | .add l r => l.arrs ++ r.arrs
  | .sub l r => l.arrs ++ r.arrs
  | .mul l r => l.arrs ++ r.arrs
  | .div l r => l.arrs ++ r.arrs
  | .read a i => a :: i.arrs
  | .len a => [a]

/-- Variables read by an expression. -/
def readVars : Expr → List Var
  | .const _ => []
  | .var x => [x]
  | .add l r => l.readVars ++ r.readVars
  | .sub l r => l.readVars ++ r.readVars
  | .mul l r => l.readVars ++ r.readVars
  | .div l r => l.readVars ++ r.readVars
  | .read _ i => i.readVars
  | .len _ => []

end Expr

namespace BExp

/-- Array indices mentioned by a condition. -/
def arrs : BExp → List Arr
  | .cmp _ l r => l.arrs ++ r.arrs
  | .not b => b.arrs
  | .and l r => l.arrs ++ r.arrs
  | .or l r => l.arrs ++ r.arrs

/-- Variables read by a condition. -/
def readVars : BExp → List Var
  | .cmp _ l r => l.readVars ++ r.readVars
  | .not b => b.readVars
  | .and l r => l.readVars ++ r.readVars
  | .or l r => l.readVars ++ r.readVars

end BExp

namespace Cmd

/-- All program points mentioned by a command, in source pre-order. `Program.WF`
requires this to be exactly `0 .. maxPoint`, so points are dense and unique. -/
def points : Cmd → List Point
  | .skip p => [p]
  | .assign p _ _ => [p]
  | .store p _ _ _ => [p]
  | .assert p _ => [p]
  | .ite p _ t e => p :: (t.points ++ e.points)
  | .while p _ body => p :: body.points
  | .seq a b => a.points ++ b.points

/-- Array indices mentioned anywhere in a command. -/
def arrs : Cmd → List Arr
  | .skip _ => []
  | .assign _ _ e => e.arrs
  | .store _ a i v => a :: (i.arrs ++ v.arrs)
  | .assert _ b => b.arrs
  | .ite _ b t e => b.arrs ++ (t.arrs ++ e.arrs)
  | .while _ b body => b.arrs ++ body.arrs
  | .seq a b => a.arrs ++ b.arrs

/-- Variables read anywhere in a command. -/
def readVars : Cmd → List Var
  | .skip _ => []
  | .assign _ _ e => e.readVars
  | .store _ _ i v => i.readVars ++ v.readVars
  | .assert _ b => b.readVars
  | .ite _ b t e => b.readVars ++ (t.readVars ++ e.readVars)
  | .while _ b body => b.readVars ++ body.readVars
  | .seq a b => a.readVars ++ b.readVars

/-- Variables assigned somewhere in a command. This is a flow-insensitive
"every read variable is assigned somewhere" check; the real frontend can be
flow-sensitive and stricter. -/
def assignedVars : Cmd → List Var
  | .skip _ => []
  | .assign _ x _ => [x]
  | .store _ _ _ _ => []
  | .assert _ _ => []
  | .ite _ _ t e => t.assignedVars ++ e.assignedVars
  | .while _ _ body => body.assignedVars
  | .seq a b => a.assignedVars ++ b.assignedVars

end Cmd

/-- A conservative bound on the number of source program points. The parser is
expected to enforce it before constructing a `Program`; `Program.compileChecked`
also checks it before allocating the instruction array. -/
def maxProgramPoints : Nat := 65536

/-- A conservative bound on the number of declared arrays. Like
`maxProgramPoints`, this is a frontend resource contract: `compileChecked`
rejects programs outside it rather than allocating for them. -/
def maxArrays : Nat := 4096

/-- A conservative bound on a declared array length. It keeps `State.init`'s
allocation bounded and is well below `i32Max`, so `Expr.len` is defined for every
accepted array. -/
def maxArrayLength : Nat := 1048576

/-- A bound on the total number of declared cells across all arrays. The
per-array and array-count bounds alone still allow `maxArrays * maxArrayLength`
cells; this caps the product that `State.init` may be asked to allocate. -/
def maxTotalArrayCells : Nat := 1048576

/-- Boolean equality for variable names, kept explicit so the well-formedness
check stays computable and axiom-free. -/
def varEq (x y : Var) : Bool :=
  match String.decEq x y with
  | isTrue _ => true
  | isFalse _ => false

/-- Boolean membership for the `Program.WF` variable check. -/
def varMem (x : Var) (vars : List Var) : Bool :=
  vars.any (fun y => varEq x y)

/-- `varMem` is sound for list membership. It is the computable membership the
domain evaluators use, so their proofs do not depend on classical decidability
of `List.Mem`. -/
theorem varMem_sound {x : Var} {vars : List Var} (h : varMem x vars = true) :
    x ∈ vars := by
  unfold varMem at h
  rcases List.any_eq_true.mp h with ⟨y, hy, hxy⟩
  have hxy' : x = y := by
    cases hd : String.decEq x y with
    | isTrue hEq => exact hEq
    | isFalse hne =>
        have hfalse : varEq x y = false := by simp [varEq, hd]
        rw [hfalse] at hxy
        simp at hxy
  simpa [hxy'] using hy

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
def entry (program : Program) : Point := program.body.entry

end Program

/-! ## State (M1.4) -/

/-- Pointwise update of a total function at one argument.

Lean core does not provide `Function.update`, and the trusted tree deliberately
does not depend on Mathlib, so this small utility (and its lemmas) lives here. -/
def funUpdate {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem funUpdate_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    funUpdate f a b a = b := by
  simp [funUpdate]

theorem funUpdate_noteq {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (h : x ≠ a) (b : β) :
    funUpdate f a b x = f x := by
  simp [funUpdate, h]

@[simp] theorem funUpdate_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) :
    funUpdate f a (f a) = f := by
  funext x
  by_cases h : x = a <;> simp [funUpdate, h]

@[simp] theorem funUpdate_funUpdate_same {α β : Type} [DecidableEq α]
    (f : α → β) (a : α) (b c : β) :
    funUpdate (funUpdate f a b) a c = funUpdate f a c := by
  funext x
  by_cases h : x = a <;> simp [funUpdate, h]

theorem funUpdate_funUpdate_noteq {α β : Type} [DecidableEq α]
    (f : α → β) {a b : α} (h : a ≠ b) (v w : β) :
    funUpdate (funUpdate f a v) b w = funUpdate (funUpdate f b w) a v := by
  funext x
  by_cases hx : x = a
  · simp [funUpdate, hx, h]
  · by_cases hy : x = b
    · have hba : b ≠ a := fun hba => h hba.symm
      simp [funUpdate, hy, hba]
    · simp [funUpdate, hx, hy]

/-- A program state: a total environment and a total memory.

Both are total functions, so evaluation can never get stuck on a missing
variable or array (plan M1.4). The frontend rejects unbound names, but the
semantics does not rely on that. -/
structure State : Type where
  /-- Variable environment. -/
  env : Var → I32
  /-- Array memory. -/
  mem : Arr → Array I32

namespace State

/-- Read a variable. Total: an unwritten variable reads as whatever `env` holds
(zero in `init`). -/
def get (s : State) (x : Var) : I32 := s.env x

/-- Write a variable. -/
def set (s : State) (x : Var) (v : I32) : State :=
  { s with env := funUpdate s.env x v }

/-- Read an array. Total: an undeclared array number reads as the empty array. -/
def memAt (s : State) (a : Arr) : Array I32 := s.mem a

/-- Replace a whole array. -/
def setMem (s : State) (a : Arr) (arr : Array I32) : State :=
  { s with mem := funUpdate s.mem a arr }

/-- The initial state of a program: every variable is zero, and every declared
array is allocated to its constant length and zero-filled.

An array number outside `Program.arrays` gets the empty array: the frontend
rejects such programs, and the semantics stays total regardless. -/
def init (p : Program) : State :=
  { env := fun _ => I32.zero,
    mem := fun a => Array.replicate (p.arrays.getD a 0) I32.zero }

@[simp] theorem get_set_same (s : State) (x : Var) (v : I32) :
    (s.set x v).get x = v := by
  simp [get, set, funUpdate]

theorem get_set_noteq (s : State) {x y : Var} (h : y ≠ x) (v : I32) :
    (s.set x v).get y = s.get y := by
  simp [get, set, funUpdate, h]

@[simp] theorem set_get (s : State) (x : Var) : s.set x (s.get x) = s := by
  cases s
  simp [set, get, funUpdate_self]

@[simp] theorem set_set_same (s : State) (x : Var) (v w : I32) :
    (s.set x v).set x w = s.set x w := by
  cases s
  simp [set, funUpdate_funUpdate_same]

theorem set_set_noteq (s : State) {x y : Var} (h : x ≠ y) (v w : I32) :
    (s.set x v).set y w = (s.set y w).set x v := by
  cases s with
  | mk env mem =>
    have h' : funUpdate (funUpdate env x v) y w = funUpdate (funUpdate env y w) x v :=
      funUpdate_funUpdate_noteq (f := env) (a := x) (b := y) (h := h) v w
    simp [set, h']

@[simp] theorem memAt_setMem_same (s : State) (a : Arr) (arr : Array I32) :
    (s.setMem a arr).memAt a = arr := by
  simp [memAt, setMem, funUpdate]

theorem memAt_setMem_noteq (s : State) {a b : Arr} (h : b ≠ a) (arr : Array I32) :
    (s.setMem a arr).memAt b = s.memAt b := by
  simp [memAt, setMem, funUpdate, h]

@[simp] theorem get_init (p : Program) (x : Var) : (init p).get x = I32.zero := by
  simp [init, get]

@[simp] theorem memAt_init (p : Program) (a : Arr) :
    (init p).memAt a = Array.replicate (p.arrays.getD a 0) I32.zero := by
  simp [init, memAt]

end State

/-! ## Expression evaluation (M1.5) -/

/-- Evaluate an integer expression.

`none` means "went wrong": a zero divisor or `min / -1` in `div`, signed
overflow in `add`/`sub`/`mul`, or an out-of-bounds `read`. Those four cases are
exactly the safety properties the project certifies, which is why this function
is where the safety property is defined (plan M1.5). `len` is total except for a
length beyond the machine range, which constant array bounds rule out.

Operands are evaluated left to right; since both are evaluated, the order does
not change the result (any failure yields `none`). -/
def eval : Expr → State → Option I32
  | .const n, _ => some n
  | .var x, s => some (s.get x)
  | .add l r, s => eval l s >>= fun a => eval r s >>= fun b => I32.add? a b
  | .sub l r, s => eval l s >>= fun a => eval r s >>= fun b => I32.sub? a b
  | .mul l r, s => eval l s >>= fun a => eval r s >>= fun b => I32.mul? a b
  | .div l r, s => eval l s >>= fun a => eval r s >>= fun b => I32.div? a b
  | .read a i, s =>
      eval i s >>= fun idx =>
        let arr := s.memAt a
        if 0 ≤ idx.val ∧ idx.val < (arr.size : Int) then
          some (arr.getD idx.val.toNat I32.zero)
        else none
  | .len a, s => I32.ofInt? ((s.memAt a).size : Int)

/-- Compare two machine integers. Total: comparisons themselves never fail; their
operands can. -/
def compare : CmpOp → I32 → I32 → Bool
  | .eq, a, b => decide (a.val = b.val)
  | .ne, a, b => decide (a.val ≠ b.val)
  | .lt, a, b => decide (a.val < b.val)
  | .le, a, b => decide (a.val ≤ b.val)
  | .gt, a, b => decide (b.val < a.val)
  | .ge, a, b => decide (b.val ≤ a.val)

/-- Evaluate a condition. `none` propagates any operand failure.

`and` and `or` are **strict**: both operands are evaluated. A short-circuit
language would make a partial operation on the right a *conditional* obligation
("only if the left is true"), which the checker's per-point safety predicates do
not express; strictness keeps every obligation unconditional. See the module
notes for the trade-off against C. -/
def evalB : BExp → State → Option Bool
  | .cmp op l r, s => eval l s >>= fun a => eval r s >>= fun b => some (compare op a b)
  | .not b, s => evalB b s >>= fun v => some (!v)
  | .and l r, s => evalB l s >>= fun a => evalB r s >>= fun b => some (a && b)
  | .or l r, s => evalB l s >>= fun a => evalB r s >>= fun b => some (a || b)

@[simp] theorem eval_const (n : I32) (s : State) : eval (.const n) s = some n := rfl

@[simp] theorem eval_var (x : Var) (s : State) : eval (.var x) s = some (s.get x) := rfl

@[simp] theorem eval_len (a : Arr) (s : State) :
    eval (.len a) s = I32.ofInt? ((s.memAt a).size : Int) := rfl

/-- Evaluation is deterministic: it is a function, so two `some` results must
agree. Useful when composing with `step` (M1.6). -/
theorem eval_det {e : Expr} {s : State} {a b : I32}
    (h1 : eval e s = some a) (h2 : eval e s = some b) : a = b := by
  rw [h1] at h2
  injection h2

/-- Condition evaluation is deterministic. -/
theorem evalB_det {b : BExp} {s : State} {x y : Bool}
    (h1 : evalB b s = some x) (h2 : evalB b s = some y) : x = y := by
  rw [h1] at h2
  injection h2

/-! ## Compiled CFG and one step (M1.6) -/

/-- Atomic actions executed by a CFG instruction. Branching is a separate
instruction form, so each atomic action has exactly one successor. -/
inductive AtomicCmd : Type where
  /-- Do nothing. -/
  | skip
  /-- `x := e`. -/
  | assign (x : Var) (e : Expr)
  /-- `a[i] := e`. -/
  | store (a : Arr) (i v : Expr)
  /-- `assert b`. -/
  | assert (b : BExp)
  deriving DecidableEq, Repr

/-- A CFG instruction: an atomic action with one successor, or a conditional
branch with two successors.

This is the "edge machine" the M1.3 notes committed to: one instruction is one
semantic step, loops are back edges, and there is no continuation stack. -/
inductive Instr : Type where
  /-- Execute `cmd`, then continue at `next`. -/
  | atomic (cmd : AtomicCmd) (next : Point)
  /-- Evaluate `b`; go to `then_` when true and `else_` when false. -/
  | branch (b : BExp) (then_ else_ : Point)
  deriving DecidableEq, Repr

namespace Instr

/-- Every successor point of an instruction lies inside `[0, n)`.

This is the instruction-level half of CFG well-formedness: the machine never
jumps outside its own instruction array, so `step` can only fail on a language
hazard, not on a missing successor. -/
def targetsLt (i : Instr) (n : Nat) : Prop :=
  match i with
  | .atomic _ next => next < n
  | .branch _ t e => t < n ∧ e < n

end Instr

/-- A compiled control-flow graph: an entry point and an instruction array
indexed by program point. The halt point is one past the largest program point
and holds a self-looping `skip`, so termination is a safe stutter, never a
failure. -/
structure CFG : Type where
  /-- Where execution starts. -/
  entry : Point
  /-- Instruction per point; indexed by `Point`. -/
  instrs : Array Instr
  deriving Repr

namespace CFG

/-- The instruction at a point, if the point is inside the array. -/
def instrAt (cfg : CFG) (p : Point) : Option Instr :=
  if h : p < cfg.instrs.size then some cfg.instrs[p] else none

/-- A well-formed CFG has its entry inside the instruction array, and every
instruction it can fetch has all successors inside the array.

`Program.compile_wf` shows that compilation always produces a well-formed CFG.
The predicate is the hypothesis T5 needs: without it, a successful `step` could
land on an out-of-range point, and the next `step` would fail for a reason no
certificate can rule out. -/
def WF (cfg : CFG) : Prop :=
  cfg.entry < cfg.instrs.size ∧
  ∀ (p : Point) (i : Instr), cfg.instrAt p = some i → i.targetsLt cfg.instrs.size

/-- The instruction returned by `instrAt` is the array's element at that point. -/
theorem instrAt_getElem {cfg : CFG} {p : Point} {i : Instr}
    (h : cfg.instrAt p = some i) (hp : p < cfg.instrs.size) :
    cfg.instrs[p] = i := by
  unfold instrAt at h
  simpa [hp] using h

end CFG

namespace Cmd

/-- The largest point mentioned by a command, used to size the instruction array
before compilation fills it. -/
def maxPoint : Cmd → Nat
  | .skip p => p
  | .assign p _ _ => p
  | .store p _ _ _ => p
  | .assert p _ => p
  | .ite p _ t e => max p (max t.maxPoint e.maxPoint)
  | .while p _ body => max p body.maxPoint
  | .seq a b => max a.maxPoint b.maxPoint

/-- Write one instruction at its point. The in-range proof is an argument, so an
out-of-range write is not a representable call: the compiler cannot silently
drop an instruction. -/
def place (instrs : Array Instr) (p : Point) (i : Instr) (hp : p < instrs.size) :
    Array Instr :=
  instrs.set p i hp

/-- `place` never changes the instruction array's size. -/
theorem place_size (instrs : Array Instr) (p : Point) (i : Instr)
    (hp : p < instrs.size) :
    (place instrs p i hp).size = instrs.size :=
  Array.size_set hp

/-- `place` preserves "all instructions have successors in range", provided the
instruction being written satisfies it. -/
theorem place_targetsLt {instrs : Array Instr} {n : Nat} {p : Point} {i : Instr}
    (hp : p < instrs.size)
    (hinv : ∀ (q : Point) (h : q < instrs.size), (instrs[q]).targetsLt n)
    (hi : i.targetsLt n) :
    ∀ (q : Point) (h : q < (place instrs p i hp).size),
      ((place instrs p i hp)[q]).targetsLt n := by
  intro q hq
  have hq' : q < instrs.size := by
    simpa [place, Array.size_set hp] using hq
  by_cases hqp : q = p
  · subst q
    have hplace : (place instrs p i hp)[p] = i := by
      unfold place
      exact Array.getElem_set_self hp
    rw [hplace]
    exact hi
  · have hplace : (place instrs p i hp)[q] = instrs[q] := by
      unfold place
      exact Array.getElem_set_ne hp hq' (fun hpq => hqp hpq.symm)
    rw [hplace]
    exact hinv q hq'

/-- Compile a command with continuation point `k`: where control goes after the
command finishes.

Atomic commands fall through to `k`; branches take their targets from the
sub-commands' entry points; a `while`'s false branch goes to `k` and its body
loops back to the guard. This is the continuation threading that a structural
small-step semantics would otherwise have to carry in a runtime stack.

The size bound is an argument: every write is in range by construction, and the
result records that compilation preserves the input array's size. -/
def compile (c : Cmd) (k : Point) (instrs : Array Instr)
    (hbound : c.maxPoint < instrs.size) :
    { out : Array Instr // out.size = instrs.size } :=
  match c with
  | .skip p =>
      ⟨place instrs p (.atomic .skip k) hbound,
        place_size instrs p (.atomic .skip k) hbound⟩
  | .assign p x e =>
      ⟨place instrs p (.atomic (.assign x e) k) hbound,
        place_size instrs p (.atomic (.assign x e) k) hbound⟩
  | .store p a i v =>
      ⟨place instrs p (.atomic (.store a i v) k) hbound,
        place_size instrs p (.atomic (.store a i v) k) hbound⟩
  | .assert p b =>
      ⟨place instrs p (.atomic (.assert b) k) hbound,
        place_size instrs p (.atomic (.assert b) k) hbound⟩
  | .ite p b t e =>
      have hp : p < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left p (max t.maxPoint e.maxPoint)) hbound
      have hte : max t.maxPoint e.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right p (max t.maxPoint e.maxPoint)) hbound
      have ht : t.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hte
      have he : e.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hte
      let instrs1 : Array Instr := place instrs p (.branch b t.entry e.entry) hp
      have hsize1 : instrs1.size = instrs.size :=
        place_size instrs p (.branch b t.entry e.entry) hp
      have he1 : e.maxPoint < instrs1.size := by
        rw [hsize1]
        exact he
      let inner := compile e k instrs1 he1
      have ht1 : t.maxPoint < instrs1.size := by
        rw [hsize1]
        exact ht
      have ht2 : t.maxPoint < inner.1.size := by
        rw [inner.2]
        exact ht1
      let outer := compile t k inner.1 ht2
      ⟨outer.1, by rw [outer.2, inner.2, hsize1]⟩
  | .while p b body =>
      have hp : p < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left p body.maxPoint) hbound
      have hb : body.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right p body.maxPoint) hbound
      let instrs1 : Array Instr := place instrs p (.branch b body.entry k) hp
      have hsize1 : instrs1.size = instrs.size :=
        place_size instrs p (.branch b body.entry k) hp
      have hb1 : body.maxPoint < instrs1.size := by
        rw [hsize1]
        exact hb
      let res := compile body p instrs1 hb1
      ⟨res.1, by rw [res.2, hsize1]⟩
  | .seq a b =>
      have han : a.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left a.maxPoint b.maxPoint) hbound
      have hbn : b.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right a.maxPoint b.maxPoint) hbound
      let resb := compile b k instrs hbn
      have ha1 : a.maxPoint < resb.1.size := by
        rw [resb.2]
        exact han
      let resa := compile a b.entry resb.1 ha1
      ⟨resa.1, by rw [resa.2, resb.2]⟩

/-- A command's entry point is at most its largest point. This is the bridge
between `entry` (where execution starts) and `maxPoint` (how large the
instruction array must be). -/
theorem entry_le_maxPoint : ∀ {c : Cmd}, c.entry ≤ c.maxPoint
  | .skip _ => Nat.le_refl _
  | .assign _ _ _ => Nat.le_refl _
  | .store _ _ _ _ => Nat.le_refl _
  | .assert _ _ => Nat.le_refl _
  | .ite _ _ _ _ => Nat.le_max_left _ _
  | .while _ _ _ => Nat.le_max_left _ _
  | .seq a _ => Nat.le_trans (entry_le_maxPoint (c := a)) (Nat.le_max_left _ _)

/-- Compilation never changes the instruction array's size. -/
theorem compile_size (c : Cmd) (k : Point) (instrs : Array Instr)
    (hbound : c.maxPoint < instrs.size) :
    (compile c k instrs hbound).1.size = instrs.size :=
  (compile c k instrs hbound).2

/-- Compilation preserves the invariant that every instruction's successors are
inside the array, for an array of size `n` that already satisfies it. -/
theorem compile_targetsLt {c : Cmd} {k : Point} {instrs : Array Instr} {n : Nat}
    (hsize : instrs.size = n)
    (hinv : ∀ (q : Point) (h : q < instrs.size), (instrs[q]).targetsLt n)
    (hk : k < n)
    (hbound : c.maxPoint < instrs.size) :
    ∀ (q : Point) (h : q < (compile c k instrs hbound).1.size),
      ((compile c k instrs hbound).1[q]).targetsLt n := by
  induction c generalizing k instrs with
  | skip p =>
      simpa [compile] using
        (place_targetsLt (instrs := instrs) (n := n) (p := p)
          (i := .atomic .skip k) hbound hinv hk)
  | assign p x e =>
      simpa [compile] using
        (place_targetsLt (instrs := instrs) (n := n) (p := p)
          (i := .atomic (.assign x e) k) hbound hinv hk)
  | store p a i v =>
      simpa [compile] using
        (place_targetsLt (instrs := instrs) (n := n) (p := p)
          (i := .atomic (.store a i v) k) hbound hinv hk)
  | assert p b =>
      simpa [compile] using
        (place_targetsLt (instrs := instrs) (n := n) (p := p)
          (i := .atomic (.assert b) k) hbound hinv hk)
  | ite p b t e iht ihe =>
      have hbound' : max p (max t.maxPoint e.maxPoint) < instrs.size := by
        simpa [maxPoint] using hbound
      have hp : p < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left p (max t.maxPoint e.maxPoint)) hbound'
      have hte : max t.maxPoint e.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right p (max t.maxPoint e.maxPoint)) hbound'
      have htn : t.maxPoint < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hte
        simpa [hsize] using this
      have hen : e.maxPoint < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hte
        simpa [hsize] using this
      let instrs1 : Array Instr := place instrs p (.branch b t.entry e.entry) hp
      have hsize1 : instrs1.size = n := by
        dsimp [instrs1]
        rw [place_size instrs p (.branch b t.entry e.entry) hp, hsize]
      have hinv1 : ∀ (q : Point) (h : q < instrs1.size),
          (instrs1[q]).targetsLt n := by
        dsimp [instrs1]
        exact place_targetsLt hp hinv (by
          simp [Instr.targetsLt]
          exact ⟨Nat.lt_of_le_of_lt (entry_le_maxPoint (c := t)) htn,
                 Nat.lt_of_le_of_lt (entry_le_maxPoint (c := e)) hen⟩)
      have he1 : e.maxPoint < instrs1.size := by simpa [hsize1] using hen
      let inner := compile e k instrs1 he1
      have hinner : inner.1.size = n := by
        rw [compile_size e k instrs1 he1, hsize1]
      have hinv2 : ∀ (q : Point) (h : q < inner.1.size),
          (inner.1[q]).targetsLt n :=
        ihe (k := k) (instrs := instrs1) hsize1 hinv1 hk he1
      have ht2 : t.maxPoint < inner.1.size := by simpa [hinner] using htn
      let outer := compile t k inner.1 ht2
      have hres := iht (k := k) (instrs := inner.1) hinner hinv2 hk ht2
      simpa [compile] using hres
  | «while» p b body ih =>
      have hbound' : max p body.maxPoint < instrs.size := by
        simpa [maxPoint] using hbound
      have hpn : p < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_left p body.maxPoint) hbound'
        simpa [hsize] using this
      have hbn : body.maxPoint < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_right p body.maxPoint) hbound'
        simpa [hsize] using this
      have hp : p < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left p body.maxPoint) hbound'
      let instrs1 : Array Instr := place instrs p (.branch b body.entry k) hp
      have hsize1 : instrs1.size = n := by
        dsimp [instrs1]
        rw [place_size instrs p (.branch b body.entry k) hp, hsize]
      have hinv1 : ∀ (q : Point) (h : q < instrs1.size),
          (instrs1[q]).targetsLt n := by
        dsimp [instrs1]
        exact place_targetsLt hp hinv (by
          simp [Instr.targetsLt]
          exact ⟨Nat.lt_of_le_of_lt (entry_le_maxPoint (c := body)) hbn, hk⟩)
      have hb1 : body.maxPoint < instrs1.size := by simpa [hsize1] using hbn
      have hres := ih (k := p) (instrs := instrs1) hsize1 hinv1 hpn hb1
      simpa [compile] using hres
  | seq a b iha ihb =>
      have hbound' : max a.maxPoint b.maxPoint < instrs.size := by
        simpa [maxPoint] using hbound
      have han : a.maxPoint < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hbound'
        simpa [hsize] using this
      have hbn : b.maxPoint < n := by
        have := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hbound'
        simpa [hsize] using this
      have han' : a.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hbound'
      have hbn' : b.maxPoint < instrs.size :=
        Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hbound'
      let resb := compile b k instrs hbn'
      have hres_b := ihb (k := k) (instrs := instrs) hsize hinv hk hbn'
      have hsize_b : resb.1.size = n := by
        rw [compile_size b k instrs hbn', hsize]
      have hres_b' : ∀ (q : Point) (h : q < resb.1.size),
          (resb.1[q]).targetsLt n := by
        simpa [resb] using hres_b
      have hk' : b.entry < n :=
        Nat.lt_of_le_of_lt (entry_le_maxPoint (c := b)) hbn
      have ha1 : a.maxPoint < resb.1.size := by simpa [hsize_b] using han
      have hres_a := iha (k := b.entry) (instrs := resb.1) hsize_b hres_b' hk' ha1
      simpa [compile, resb] using hres_a

end Cmd

namespace Program

/-- Total declared cells across all arrays, used by `checkWF` to bound
initialisation. -/
def arrayCells (p : Program) : Nat :=
  p.arrays.toList.foldl (fun acc n => acc + n) 0

/-- Decidable source well-formedness: the point list is exactly
`0 .. maxPoint` (dense and unique), `maxPoint` is bounded, the array count, each
declared array length, and the total declared cell count are within the resource
bounds, every array index is declared, and every read variable is assigned
somewhere.

This is the frontend contract. `Program.compile` assumes it; `compileChecked`
validates it before compiling. -/
def checkWF (p : Program) : Bool :=
  Nat.blt p.body.maxPoint maxProgramPoints &&
  Nat.blt p.arrays.size maxArrays &&
  p.arrays.toList.all (fun n => decide (n ≤ maxArrayLength)) &&
  decide (arrayCells p ≤ maxTotalArrayCells) &&
  (p.body.points.length == p.body.maxPoint + 1) &&
  (p.body.points.eraseDups.length == p.body.points.length) &&
  p.body.points.all (fun q => Nat.blt q (p.body.maxPoint + 1)) &&
  p.body.arrs.all (fun a => Nat.blt a p.arrays.size) &&
  p.body.readVars.all (fun x => varMem x p.body.assignedVars)

/-- Source well-formedness as a proposition. -/
def WF (p : Program) : Prop := p.checkWF = true

end Program

/-- Compile a program to a CFG.

The array is sized to hold every program point plus one halt slot; the halt slot
is a self-looping `skip`, so reaching it is a safe stutter rather than an error.

This is the unchecked compiler: it assumes the frontend's `Program.WF`
(dense unique points, declared arrays, assigned variables, bounded
`maxPoint`). Use `compileChecked` at an untrusted boundary. -/
def Program.compile (p : Program) : CFG :=
  let halt : Point := p.body.maxPoint + 1
  let instrs : Array Instr := Array.replicate (halt + 1) (.atomic .skip halt)
  have hbound : p.body.maxPoint < instrs.size := by
    simp [instrs, halt]
    omega
  { entry := p.entry,
    instrs := (Cmd.compile p.body halt instrs hbound).1 }

/-- **F2 — compiled CFGs are well formed.**

The entry is inside the instruction array, and every instruction the machine can
fetch sends control to a point inside the array. This is the hypothesis T5 needs:
without it, a successful `step` could land on a missing instruction and the next
`step` would fail for a reason no certificate can discharge.

The proof is the array-size bound (`maxPoint` covers every point, `place` writes
inside the array) plus the target bound (every continuation and branch target is
either a sub-command entry or the halt point). -/
theorem Program.compile_wf (p : Program) : (Program.compile p).WF := by
  let halt : Point := p.body.maxPoint + 1
  let instrs : Array Instr := Array.replicate (halt + 1) (.atomic .skip halt)
  have hbound : p.body.maxPoint < instrs.size := by
    simp [instrs, halt]
    omega
  have hk : halt < instrs.size := by
    simp [instrs, halt]
  have hinv : ∀ (q : Point) (h : q < instrs.size),
      (instrs[q]).targetsLt instrs.size := by
    intro q hq
    have hq' : q < (Array.replicate (halt + 1) (Instr.atomic AtomicCmd.skip halt)).size := by
      simpa [instrs] using hq
    rw [Array.getElem_replicate (h := hq')]
    simp [Instr.targetsLt, instrs, halt]
  have hcomp := Cmd.compile_targetsLt (c := p.body) (k := halt) (instrs := instrs)
    (n := instrs.size) rfl hinv hk hbound
  have hcomp_size : (Cmd.compile p.body halt instrs hbound).1.size = instrs.size :=
    Cmd.compile_size p.body halt instrs hbound
  constructor
  · simpa [Program.compile, Program.entry, instrs, halt, hcomp_size] using
      (Nat.lt_of_le_of_lt (Cmd.entry_le_maxPoint (c := p.body)) hbound)
  · intro q i hi
    have hq : q < (Program.compile p).instrs.size := by
      by_cases hq : q < (Program.compile p).instrs.size
      · exact hq
      · have hnone : (Program.compile p).instrAt q = none := by
          simp [CFG.instrAt, hq]
        rw [hnone] at hi
        simp at hi
    have hget : (Program.compile p).instrs[q] = i :=
      CFG.instrAt_getElem hi hq
    have hq'' : q < (Cmd.compile p.body halt instrs hbound).1.size := by
      simpa [Program.compile, instrs, halt] using hq
    have hq' : q < instrs.size := by
      simpa [hcomp_size] using hq''
    have htarget : i.targetsLt (Program.compile p).instrs.size := by
      have h := hcomp q hq''
      have h2 : (Cmd.compile p.body halt instrs hbound).1[q] = i := by
        simpa [Program.compile, instrs, halt] using hget
      rw [h2] at h
      simpa [Program.compile, instrs, halt, hcomp_size] using h
    exact htarget

/-- Validate source well-formedness before compiling. This is the fail-closed
entry point: a malformed program returns `none` instead of being silently
truncated. -/
def Program.compileChecked (p : Program) : Option CFG :=
  if p.checkWF then some (Program.compile p) else none

/-- A checked compilation only returns well-formed CFGs. -/
theorem Program.compileChecked_wf {p : Program} {cfg : CFG}
    (h : p.compileChecked = some cfg) : cfg.WF := by
  unfold Program.compileChecked at h
  cases hwf : p.checkWF with
  | true =>
      simp [hwf] at h
      rw [← h]
      exact Program.compile_wf p
  | false =>
      simp [hwf] at h

/-- A well-formed source program compiles through the checked entry point. This
is the bridge T5 uses to move from `Program.WF` to a checked compilation. -/
theorem Program.compileChecked_of_WF {p : Program} (h : p.WF) :
    p.compileChecked = some (Program.compile p) := by
  unfold Program.compileChecked
  have h' : p.checkWF = true := h
  simp [h']

namespace CFG

/-- Execute an atomic action. `none` is reserved for the four hazards; it is the
only way an atomic step can fail. -/
def exec (cmd : AtomicCmd) (s : State) : Option State :=
  match cmd with
  | .skip => some s
  | .assign x e => eval e s >>= fun v => some (s.set x v)
  | .store a i v =>
      eval i s >>= fun idx =>
      eval v s >>= fun val =>
        let arr := s.memAt a
        if h : 0 ≤ idx.val ∧ idx.val < (arr.size : Int) then
          some (s.setMem a (arr.set idx.val.toNat val))
        else none
  | .assert b => evalB b s >>= fun v => if v then some s else none

/-- One step of the compiled machine: fetch the instruction at `p`, execute it,
and move to its successor. A branch evaluates its condition and chooses a side.

`none` means a command or condition failed. An out-of-range point is also `none`
— that is a malformed CFG, not a language-level hazard. -/
def step (cfg : CFG) (p : Point) (s : State) : Option (Point × State) :=
  match cfg.instrAt p with
  | none => none
  | some (.atomic cmd next) => exec cmd s >>= fun s' => some (next, s')
  | some (.branch b t e) => evalB b s >>= fun v => some ((if v then t else e), s)

/-- **T1 — determinism.** A configuration has at most one successor.

Under the compiled edge machine this is immediate: `step` is a function, so two
successful results must be the same configuration. The plan expected an induction
on commands and on `eval`; that induction now lives in `eval_det` (M1.5) and in
`Cmd.compile`, which is deterministic by construction (M1.6). The change of
statement is recorded in `docs/THEOREMS.md`. -/
theorem step_det {cfg : CFG} {p : Point} {s : State} {c₁ c₂ : Point × State}
    (h1 : step cfg p s = some c₁) (h2 : step cfg p s = some c₂) : c₁ = c₂ := by
  rw [h1] at h2
  injection h2

/-! ## Runs and safety (M1.7) -/

/-- Run `n` steps from configuration `(p, s)`.

Fuel exhaustion is **not** failure: `run 0` returns the starting configuration,
and `none` appears only when a step itself fails. This is what lets `Safe` treat
infinite loops (and the halt stutter) as safe: every finite prefix is fine. -/
def run (cfg : CFG) : Nat → Point → State → Option (Point × State)
  | 0, p, s => some (p, s)
  | n + 1, p, s => step cfg p s >>= fun c => run cfg n c.1 c.2

/-- Safety: from the entry point, no finite number of steps ever fails.

Infinite loops are safe because every finite prefix is; divergence is not a
safety violation. This is the plan's `Safe s := ∀ n, run n s ≠ none`, with the
program's entry point and compiled machine made explicit. -/
def Safe (cfg : CFG) (s : State) : Prop := ∀ n, run cfg n cfg.entry s ≠ none

@[simp] theorem run_zero (cfg : CFG) (p : Point) (s : State) :
    run cfg 0 p s = some (p, s) := rfl

@[simp] theorem run_succ (cfg : CFG) (n : Nat) (p : Point) (s : State) :
    run cfg (n + 1) p s = step cfg p s >>= fun c => run cfg n c.1 c.2 := rfl

/-- A safe configuration cannot take a failing first step. -/
theorem safe_step {cfg : CFG} {s : State} (h : Safe cfg s) :
    (step cfg cfg.entry s).isSome = true := by
  have h1 := h 1
  cases hstep : step cfg cfg.entry s with
  | none => simp [run, hstep] at h1
  | some c => simp

/-- One failing step refutes safety. -/
theorem not_safe_of_step_none {cfg : CFG} {s : State}
    (h : step cfg cfg.entry s = none) : ¬ Safe cfg s := by
  intro hs
  have h1 := hs 1
  simp [run, h] at h1

/-- `Safe` in terms of `isSome`, which is the form the later proofs use. -/
theorem safe_iff_isSome {cfg : CFG} {s : State} :
    Safe cfg s ↔ ∀ n, (run cfg n cfg.entry s).isSome = true := by
  constructor
  · intro h n
    exact Option.isSome_iff_ne_none.mpr (h n)
  · intro h n
    exact Option.isSome_iff_ne_none.mp (h n)

/-- **T2 — safety as the absence of a failing prefix.**

`Safe` is *defined* as the finite-prefix property (`∀ n, run n ≠ none`), so the
plan's literal `Safe ↔ ∀ n, run n ≠ none` would be `Iff.rfl`. This is the
equivalent statement the project actually uses: there is no fuel at which a run
fails. The induction escape hatch is the definition itself — every later proof is
an ordinary induction on the step count, never a coinductive argument. The change
of statement is recorded in `docs/THEOREMS.md`. -/
theorem safe_iff {cfg : CFG} {s : State} :
    Safe cfg s ↔ ¬ ∃ n, run cfg n cfg.entry s = none := by
  constructor
  · intro h hbad
    rcases hbad with ⟨n, hn⟩
    exact h n hn
  · intro h n hn
    exact h ⟨n, hn⟩

/-- The finite-prefix form: every amount of fuel yields a configuration. -/
theorem safe_iff_exists {cfg : CFG} {s : State} :
    Safe cfg s ↔ ∀ n, ∃ c, run cfg n cfg.entry s = some c := by
  constructor
  · intro h n
    cases hrun : run cfg n cfg.entry s with
    | none => exact absurd hrun (h n)
    | some c => exact ⟨c, rfl⟩
  · intro h n
    rcases h n with ⟨c, hc⟩
    rw [hc]
    simp

end CFG

namespace Program

/-- A program is safe when it is **well formed** and its compiled machine is safe
from the initial state.

The `WF` conjunct is deliberate: a malformed source program has no meaning, so it
is never certified safe. The checker must establish `Program.WF` (a decidable
check) before a certificate can be accepted; this is the source contract T5
carries into its conclusion. -/
def safe (p : Program) : Prop :=
  WF p ∧ CFG.Safe (Program.compile p) (State.init p)

end Program

/-! ## Edges (M1.8) -/

/-- The command on a checker-facing edge: either an atomic action, or a guard
assumption recording which way a branch was taken.

`assume b true` means the edge is taken when `b` evaluates to `true`; `assume b
false` means when it evaluates to `false`. These are what the checker's transfer
function refines on, and they are why a branch needs no target-dependent
transfer. -/
inductive EdgeCmd : Type where
  /-- An atomic action. -/
  | atomic (cmd : AtomicCmd)
  /-- A branch guard: the edge is taken when `b` is `positive`. -/
  | assume (b : BExp) (positive : Bool)
  deriving DecidableEq, Repr

/-- A checker-facing edge `(p, cmd, q)`: the checker's obligations are indexed by
these. -/
structure Edge : Type where
  /-- Source point. -/
  src : Point
  /-- Command executed on the edge. -/
  cmd : EdgeCmd
  /-- Target point. -/
  dst : Point
  deriving DecidableEq, Repr

namespace EdgeCmd

/-- Execute the effect of a checker edge. An `assume` edge is the identity on
states when its guard has the required polarity, and fails otherwise.

This is the edge-level counterpart of `CFG.exec`: `step_edge` proves that every
successful `step` is exactly one edge effect plus a control transfer. It is the
semantics that `transfer_sound` will be stated against. -/
def exec : EdgeCmd → State → Option State
  | .atomic cmd, s => CFG.exec cmd s
  | .assume b true, s => if evalB b s = some true then some s else none
  | .assume b false, s => if evalB b s = some false then some s else none

end EdgeCmd

namespace Instr

/-- The edges emitted by one instruction at point `p`: one for an atomic action,
two for a branch (guard true and guard false). -/
def edgesAt (p : Point) : Instr → List Edge
  | .atomic cmd next => [{ src := p, cmd := .atomic cmd, dst := next }]
  | .branch b t e =>
      [{ src := p, cmd := .assume b true, dst := t },
       { src := p, cmd := .assume b false, dst := e }]

/-- Every edge emitted by an instruction lands inside `n`. -/
theorem edgesAt_dst_lt {i : Instr} {n : Nat} {p : Point}
    (h : i.targetsLt n) : ∀ edge ∈ i.edgesAt p, edge.dst < n := by
  intro edge he
  cases i with
  | atomic cmd next =>
      simp [edgesAt] at he
      subst edge
      simpa [targetsLt] using h
  | branch b t e =>
      simp [edgesAt] at he
      rcases he with rfl | rfl
      · have h' : t < n ∧ e < n := by simpa [targetsLt] using h
        exact h'.1
      · have h' : t < n ∧ e < n := by simpa [targetsLt] using h
        exact h'.2

end Instr

namespace CFG

/-- All edges of the compiled graph, in ascending point order. The checker
recomputes this from the AST; the analyzer never supplies it.

Every point in the instruction array contributes its edges, including the halt
point (a `skip` self-loop), so the projection covers the whole graph. -/
def edges (cfg : CFG) : List Edge :=
  List.flatMap
    (fun p =>
      match cfg.instrAt p with
      | none => []
      | some i => i.edgesAt p)
    (List.range cfg.instrs.size)

/-- A well-formed CFG's edge projection has no out-of-range destination. This is
the edge-indexed form of `WF`, convenient for the checker's obligations. -/
theorem WF.edges_dst_lt {cfg : CFG} (h : cfg.WF) :
    ∀ e ∈ cfg.edges, e.dst < cfg.instrs.size := by
  intro e he
  unfold edges at he
  rw [List.mem_flatMap] at he
  rcases he with ⟨p, hp, he⟩
  have hplt : p < cfg.instrs.size := List.mem_range.mp hp
  cases hi : cfg.instrAt p with
  | none => simp [hi] at he
  | some i =>
      simp [hi] at he
      exact Instr.edgesAt_dst_lt (h.2 p i hi) e he

/-- A point at which `instrAt` returns an instruction is inside the array. -/
theorem instrAt_lt {cfg : CFG} {p : Point} {i : Instr} (h : cfg.instrAt p = some i) :
    p < cfg.instrs.size := by
  unfold instrAt at h
  by_cases hp : p < cfg.instrs.size
  · exact hp
  · simp [hp] at h

/-- An edge emitted by the instruction at `p` is an edge of the graph. -/
theorem mem_edges_of_mem_edgesAt {cfg : CFG} {p : Point} {i : Instr} {e : Edge}
    (hi : cfg.instrAt p = some i) (he : e ∈ i.edgesAt p) : e ∈ cfg.edges := by
  unfold edges
  rw [List.mem_flatMap]
  exact ⟨p, List.mem_range.mpr (instrAt_lt hi), by simp [hi, he]⟩

/-- The edge of an atomic instruction is an edge of the graph. -/
theorem mem_edges_atomic {cfg : CFG} {p : Point} {cmd : AtomicCmd} {next : Point}
    (h : cfg.instrAt p = some (.atomic cmd next)) :
    ({ src := p, cmd := .atomic cmd, dst := next } : Edge) ∈ cfg.edges :=
  mem_edges_of_mem_edgesAt h (by simp [Instr.edgesAt])

/-- The guard-true edge of a branch is an edge of the graph. -/
theorem mem_edges_branch_true {cfg : CFG} {p : Point} {b : BExp} {t e : Point}
    (h : cfg.instrAt p = some (.branch b t e)) :
    ({ src := p, cmd := .assume b true, dst := t } : Edge) ∈ cfg.edges :=
  mem_edges_of_mem_edgesAt h (by simp [Instr.edgesAt])

/-- The guard-false edge of a branch is an edge of the graph. -/
theorem mem_edges_branch_false {cfg : CFG} {p : Point} {b : BExp} {t e : Point}
    (h : cfg.instrAt p = some (.branch b t e)) :
    ({ src := p, cmd := .assume b false, dst := e } : Edge) ∈ cfg.edges :=
  mem_edges_of_mem_edgesAt h (by simp [Instr.edgesAt])

/-- **every successful step is one edge of the graph.**

The step relation and the edge projection are two views of the same machine:
`step` is deterministic and chooses one instruction; `edges` lists both branch
outcomes. This theorem says a successful step corresponds to an edge with the
same source, the same destination, and an edge effect `EdgeCmd.exec` that
produces the same state. The `assume` cases are the branch-polarity link; the
`atomic` case is the effect link.

This is the bridge T5 needs: it can turn an edge obligation (indexed by `edges`)
into a statement about the actual transition taken by `step`. -/
theorem step_edge {cfg : CFG} {p : Point} {s : State} {q : Point} {s' : State}
    (h : step cfg p s = some (q, s')) :
    ∃ e ∈ cfg.edges,
      e.src = p ∧ e.dst = q ∧ e.cmd.exec s = some s' := by
  cases hi : cfg.instrAt p with
  | none => simp [step, hi] at h
  | some i =>
      cases i with
      | atomic cmd nxt =>
          simp only [step, hi] at h
          change Option.bind (exec cmd s) (fun s'' => some (nxt, s'')) =
            some (q, s') at h
          simp only [Option.bind_eq_some_iff] at h
          rcases h with ⟨s'', hs'', hsome⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          rcases hsome with ⟨hnext, hstate⟩
          refine ⟨{ src := p, cmd := .atomic cmd, dst := nxt }, ?_, rfl, hnext, ?_⟩
          · exact mem_edges_atomic (by simpa using hi)
          · simp [EdgeCmd.exec, hs'', hstate]
      | branch b t e =>
          simp only [step, hi] at h
          change Option.bind (evalB b s)
            (fun v => some ((if v then t else e), s)) = some (q, s') at h
          simp only [Option.bind_eq_some_iff] at h
          rcases h with ⟨v, hv, hsome⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          rcases hsome with ⟨hq, hstate⟩
          cases v with
          | false =>
              refine ⟨{ src := p, cmd := .assume b false, dst := e },
                ?_, rfl, ?_, ?_⟩
              · exact mem_edges_branch_false (by simpa using hi)
              · simpa using hq
              · simp only [EdgeCmd.exec, hv]
                exact congrArg some hstate
          | true =>
              refine ⟨{ src := p, cmd := .assume b true, dst := t },
                ?_, rfl, ?_, ?_⟩
              · exact mem_edges_branch_true (by simpa using hi)
              · simpa using hq
              · simp only [EdgeCmd.exec, hv]
                exact congrArg some hstate

end CFG

end CertCore
