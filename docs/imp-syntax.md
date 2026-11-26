# `Imp` surface syntax

The toy language the certificates are about. There is no parser in the trusted
tree yet; this document is the normative specification for the three fixtures in
`examples/` and the target the frontend (and the Haskell mirror) must agree on.

## Lexical

- Identifiers: `[A-Za-z_][A-Za-z0-9_]*`.
- Numbers: decimal, optionally with a leading `-` in operand position; a literal
  must fit signed 32-bit. Out-of-range literals are a **frontend error**, not a
  runtime failure (the AST stores `I32`).
- Comments: `//` to end of line.
- Keywords: `skip`, `assert`, `if`, `else`, `while`, `array`, `len`.

## Grammar

```ebnf
program   ::= decl* stmt*
decl      ::= "array" IDENT "[" NUM "]" ";"
stmt      ::= "skip" ";"
            | IDENT ":=" expr ";"
            | IDENT "[" expr "]" ":=" expr ";"
            | "assert" "(" boolExpr ")" ";"
            | "if" "(" boolExpr ")" block ("else" block)?
            | "while" "(" boolExpr ")" block
            | block
block     ::= "{" stmt* "}"
expr      ::= expr ("+" | "-") term | term
term      ::= term ("*" | "/") atom | atom
atom      ::= NUM | "-" NUM | IDENT | IDENT "[" expr "]" | "len" "(" IDENT ")" | "(" expr ")"
boolExpr  ::= boolExpr "||" boolTerm | boolTerm
boolTerm  ::= boolTerm "&&" boolFactor | boolFactor
boolFactor::= "!" boolFactor | "(" boolExpr ")" | expr CMP expr
CMP       ::= "==" | "!=" | "<" | "<=" | ">" | ">="
```

Operators associate to the left; `*` and `/` bind tighter than `+` and `-`;
`&&` binds tighter than `||`; `!` binds tightest. Parentheses override.

## Meaning

- Variables and arrays are **zero-initialised**; `State` is total, so an unwritten
  variable reads 0. The frontend should still reject reads of never-assigned
  variables; the semantics does not need to.
- `array a[n];` declares `a` with constant length `n`; array numbers follow
  declaration order (`a` is 0, the next is 1, …), matching `Program.arrays`.
- `/` is **truncating** integer division (toward zero, C/x86 `idiv`). `x / 0` and
  `min / -1` are failures.
- Arithmetic overflow is a failure, not a wrap. `x + 1` at `x = 2147483647`
  fails.
- `a[i]` and `a[i] := v` fail when `i` is outside `[0, n)`.
- `assert(b)` fails when `b` is false.
- `&&` and `||` are **strict**: both operands are evaluated, so a failing
  division on either side fails the condition. (This differs from C.)
- A failing operation is a *stuck* state (`none`), which is exactly what the
  checker's safety obligations rule out.

## Program points

Each atomic command (`skip`, assignment, store, `assert`) and each branch point
(`if`, `while`) gets a program point. The frontend will assign them in source
pre-order starting at 0; the compiled CFG adds one halt point after the largest
point. `.imp` files carry no points — they are assigned from the source text.

The frontend must construct a `Program` satisfying `Program.checkWF`: points are
exactly `0 .. maxPoint` (dense and unique), `maxPoint < 65536`, every array index
is within the declared array count, and every read variable is assigned
somewhere. `Program.compileChecked` returns `none` for a program that fails this
contract; the parser should use it (or the same checks) at the source boundary.

## Fixtures

| File | Expected |
|---|---|
| [`examples/safe.imp`](../examples/safe.imp) | runs to halt, `x = 3`, `y = 1`, no failure |
| [`examples/div-zero.imp`](../examples/div-zero.imp) | fails at `10 / x` with `x = 0` |
| [`examples/array-overflow.imp`](../examples/array-overflow.imp) | fails storing `a[3]` in an array of length 3 |

The Lean-side encodings of the same programs live in
`lean/Tests/Examples.lean`, with the expected `run` outcomes pinned.
