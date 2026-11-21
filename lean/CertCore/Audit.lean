/-!
# `CertCore.Audit` — trusted

The axiom-footprint audit (project plan D10, §14). Run with:

    lake env lean lean/CertCore/Audit.lean

Expected output once T5 exists (M3.8):

    'check_sound' depends on axioms: [propext, Quot.sound]

or the strictly smaller "does not depend on any axioms". Anything else — in
particular `sorryAx` or `Classical.choice` — is a soundness hole and must fail
CI (M11.4).

Status: **stub** (M0). The `#print axioms` commands are added with the
theorems they audit; there is nothing to audit yet.
-/
