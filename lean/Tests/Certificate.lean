import CertCore.Cert

/-!
# Certificate-type tests (M3.1)

Run with:

    lake env lean lean/Tests/Certificate.lean

Pins the row-major lookup semantics: `some (some a)` is an abstract state,
`some none` is the v1 `bot` marker, and `none` is a missing key (`⊤`).
-/

open CertCore

def cert : Certificate Nat :=
  Certificate.ofSparse 2 3
    { point := 0, label := 0, state := some 7 }
    [ { point := 1, label := 0, state := some 42 },
      { point := 1, label := 1, state := none },
      { point := 2, label := 0, state := some 0 } ]

#guard cert.entryPoint = 0
#guard cert.entryLabel = 0
#guard cert.entryState = some 7
#guard cert.labels = 2
#guard cert.points = 3

#guard cert.lookup? 1 0 = some (some 42)
#guard cert.lookup? 1 1 = some none
#guard cert.lookup? 2 0 = some (some 0)

-- A missing key is `⊤`, not `bot`.
#guard cert.lookup? 3 0 = none
#guard cert.lookup? 1 2 = none
#guard !cert.isBot? 3 0
#guard cert.isBot? 1 1

-- The raw lookup distinguishes absent from present-`bot`.
#guard (cert.find? 1 1).isSome
#guard (cert.find? 3 0).isNone
