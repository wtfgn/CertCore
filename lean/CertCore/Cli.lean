import CertCore.Cert

/-!
# `certcore` — command-line entry point

M4.5 turns this into `certcore check <program.imp> <cert.json>` with exit
codes 0 (accept), 1 (reject), 2 (malformed). At M1 it only proves that the
executable target builds and runs.
-/

namespace CertCore

/-- Version string of the artifact. -/
def version : String := "0.1.0"

end CertCore

def main : IO Unit :=
  IO.println s!"certcore {CertCore.version} (M1 semantics core: checker not implemented yet)"
