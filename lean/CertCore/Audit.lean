import CertCore.Semantics

/-!
# `CertCore.Audit` — trusted

The axiom-footprint audit (project plan D10, §14). Run with:

    lake env lean lean/CertCore/Audit.lean

At M1 the script prints the footprint of the proved semantics lemmas. Every line
should be `[propext, Quot.sound]` or strictly smaller. Anything else — in
particular `sorryAx` or `Classical.choice` — is a soundness hole.

Status: **M1 audit.** T1/T2, `Program.compile_wf`, and `CFG.step_edge` are the
M1 theorems. M3.8 adds `#print axioms check_sound`; M11.4 turns the comparison
into a CI gate.
-/

namespace CertCore

#print axioms I32.ofIntWrap_agrees
#print axioms CFG.step_det
#print axioms CFG.safe_iff
#print axioms CFG.safe_iff_exists
#print axioms Program.compile_wf
#print axioms CFG.step_edge

end CertCore
