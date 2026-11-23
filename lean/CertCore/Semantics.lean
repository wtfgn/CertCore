import CertCore.I32

/-!
# `CertCore.Semantics` — trusted

Abstract syntax, configurations, the fuel-indexed deterministic small-step
semantics, and the safety predicate `Safe`.

Status: **syntax, state and expression evaluation complete (M1.2–M1.5); command
semantics pending (M1.6–M1.7)**. This module is inside the TCB: a bug here
changes what "safe" means (plan §10.1).

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

Pending:

* `step`, `run`, `Safe` (M1.6–M1.7).
* `edges` (M1.8), T1 `step_det` (M1.9), T2 `safe_iff` (M1.10).

Decisions that matter later:

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

end CertCore
