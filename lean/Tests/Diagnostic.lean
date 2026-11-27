import CertCore.Check

/-!
# Diagnostic tests (M3.2)

Run with:

    lake env lean lean/Tests/Diagnostic.lean

Pins the typed rejection value and the `Except` plumbing the checker will use.
-/

open CertCore

def e : Edge := { src := 1, cmd := .atomic .skip, dst := 2 }

#guard (Diagnostic.malformed (Abs := Nat) "bad json").kind = .malformed
#guard (Diagnostic.unsupportedDomain (Abs := Nat) "octagon").kind = .unsupportedDomain
#guard (Diagnostic.hashMismatch (Abs := Nat) "abc").kind = .hashMismatch

#guard (Diagnostic.init 0 0 1 2).kind = .init
#guard (Diagnostic.init 0 0 1 2).point = some 0
#guard (Diagnostic.init 0 0 1 2).label = some 0
#guard (Diagnostic.init 0 0 1 2).expected = some 1
#guard (Diagnostic.init 0 0 1 2).actual = some 2

#guard (Diagnostic.ofEdge e 0 3 4).kind = .edge
#guard (Diagnostic.ofEdge e 0 3 4).edge = some e
#guard (Diagnostic.ofEdge e 0 3 4).point = some 1
#guard (Diagnostic.ofEdge e 0 3 4).expected = some 3
#guard (Diagnostic.ofEdge e 0 3 4).actual = some 4

#guard (Diagnostic.safety 5 1 7).kind = .safety
#guard (Diagnostic.safety 5 1 7).point = some 5
#guard (Diagnostic.safety 5 1 7).detail = ""

def ok : CheckResult Nat Nat := .ok 42
def bad : CheckResult Nat Nat := .error (Diagnostic.malformed "bad json")

#guard ok.isOk
#guard (match bad with | .error _ => true | .ok _ => false)
#guard (match bad with | .error d => d.kind = .malformed | .ok _ => false)
