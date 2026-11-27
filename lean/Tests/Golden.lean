import CertCore.Proofs
import CertCore.Domain.IntervalInstance

/-!
# Golden accept (M3.9)

Run with:

    lake env lean lean/Tests/Golden.lean

A non-trivial program (`x := 4; y := 8 / x; assert y = 2`) with a sparse
certificate is accepted by `check`, and `check_sound` turns that acceptance into
`Program.safe`.
-/

open CertCore
open CertCore.Interval

def c (n : Int) : I32 := I32.ofIntWrap n

def p : Program :=
  { body := .seq (.assign 0 "x" (.const (c 4)))
      (.seq (.assign 1 "y" (.div (.const (c 8)) (.var "x")))
        (.assert 2 (.cmp .eq (.var "y") (.const (c 2))))),
    arrays := #[] }

def D : CertDomain :=
  intervalDomain (fun a => p.arrays.getD a 0) ["x", "y"] []

def st (x y : Int) : Interval.Abs :=
  { vars := fun v =>
      if v = "x" then Interval.toInterval (c x)
      else if v = "y" then Interval.toInterval (c y)
      else Interval.top,
    mem := fun _ => Interval.top }

def cert : Certificate D.Abs :=
  Certificate.ofSparse 1 4
    { point := 0, label := 0, state := some (D.initOf p) }
    [ { point := 1, label := 0, state := some (st 4 0) },
      { point := 2, label := 0, state := some (st 4 2) } ]

#guard cert.wellFormed p
#guard (check D p cert).isOk

theorem golden_check : check D p cert = .ok () := by
  rfl

theorem golden_safe : Program.safe p :=
  check_sound (D := D) (p := p) (cert := cert) (POn_init p) golden_check

-- The same certificate with one corrupted target is rejected end-to-end.
def badCert : Certificate D.Abs :=
  Certificate.ofSparse 1 4
    { point := 0, label := 0, state := some (D.initOf p) }
    [ { point := 1, label := 0, state := some (st 4 0) },
      { point := 2, label := 0, state := some (st 4 3) } ]

#guard !(check D p badCert).isOk