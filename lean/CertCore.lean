import CertCore.I32
import CertCore.Semantics
import CertCore.Domain
import CertCore.Domain.Interval
import CertCore.Domain.IntervalTransfer
import CertCore.Domain.IntervalArrays
import CertCore.Cert
import CertCore.Check
import CertCore.Proofs

/-!
# `CertCore` — umbrella module for the trusted library

Imports every trusted module so that `lake build` checks the whole tree and
`import CertCore` gives the full kernel. `CertCore.Audit` is deliberately not
imported here: it is a script run with `lake env lean CertCore/Audit.lean`, and
`CertCore.Cli` is the executable root.
-/
