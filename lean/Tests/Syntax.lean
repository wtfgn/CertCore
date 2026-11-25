import CertCore.Semantics

/-!
# `Cmd` / `Program` smoke tests

Build-time checks of the M1.3 syntax layer. Run with:

    lake env lean lean/Tests/Syntax.lean

The AST is data, so the meaningful property to pin here is `entry`: the derived
entry point must agree with the first executed command, including through nested
`seq` and the branch formers. Everything is a `#guard`, so a wrong expectation
fails the build (elaboration-time evaluation, not a proof).
-/

open CertCore

/-- In-range test constant. -/
def c (n : Int) : I32 := I32.ofIntWrap n

/-- A program that uses every command former. -/
def sample : Program where
  body :=
    .seq (.assign 0 "x" (.const (c 0)))
      (.while 1 (.cmp .lt (.var "x") (.const (c 10)))
        (.seq (.assign 2 "x" (.add (.var "x") (.const (c 1))))
              (.store 3 0 (.var "x") (.const (c 42)))))
  arrays := #[10]

#guard Program.entry sample = some 0

-- `seq` takes its first component's entry, recursively.
#guard Cmd.entry (.seq (.skip 7) (.assign 8 "x" (.const (c 1)))) = 7
#guard Cmd.entry (.seq (.seq (.skip 1) (.skip 2)) (.skip 3)) = 1

-- Branch and loop formers are their own points.
#guard Cmd.entry (.ite 6 (.cmp .eq (.var "x") (.const (c 0))) (.skip 7) (.skip 8)) = 6
#guard Cmd.entry (.while 4 (.cmp .lt (.var "x") (.const (c 10))) (.skip 5)) = 4

-- Structural equality is syntactic: points distinguish otherwise identical commands.
#guard (Cmd.skip 0) ≠ (Cmd.skip 1)
#guard sample ≠ ({ sample with body := .skip 0 } : Program)
