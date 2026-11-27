import CertCore.Domain.IntervalInstance

/-!
# `CertCore.Audit` — trusted

The axiom-footprint audit (project plan D10, §14). Run with:

    lake env lean lean/CertCore/Audit.lean

Every line should be `[propext, Quot.sound]` or strictly smaller. `Classical.choice`
or `sorryAx` appearing is a failure: CI runs this script and fails on either.

M1 (semantics, T1/T2, the compiler/bridge), M2 (the interval domain and its T4
fields), and F1 (the checker interface: `initOf`/`init_sound`,
`entails`/`entails_sound`, `P_step`) are all listed below. M3.8 adds
`check_sound`; M11.4 keeps this comparison as a CI gate.
-/

namespace CertCore

/-! ## M1: machine integers, semantics, CFG, edges -/

#print axioms I32.ofIntWrap_agrees
#print axioms varMem_sound
#print axioms CFG.step_det
#print axioms CFG.safe_iff
#print axioms CFG.safe_iff_exists
#print axioms Program.compile_wf
#print axioms Program.compileChecked_wf
#print axioms CFG.step_edge

/-! ## M2: interval values, T4a/T4b/top, arithmetic and arrays -/

#print axioms Interval.gamma_toInterval
#print axioms Interval.gamma_toInterval_iff
#print axioms Interval.ble_sound
#print axioms Interval.ble_complete
#print axioms Interval.exists_gamma
#print axioms Interval.join_sound
#print axioms Interval.top_sound
#print axioms Interval.add_sound
#print axioms Interval.sub_sound
#print axioms Interval.idxWithin_sound
#print axioms Interval.meet_sound
#print axioms Interval.singleton?_sound
#print axioms Interval.div_sound
#print axioms Interval.evalExprAbsOn_sound
#print axioms Interval.assignAbsOn_sound
#print axioms Interval.storeAbsOn_sound
#print axioms Interval.bleAbs_sound
#print axioms Interval.joinAbs_sound
#print axioms Interval.transferAbs_sound
#print axioms Interval.refineVar_sound
#print axioms Interval.refineAbs_sound

/-! ## F1: the checker interface -/

#print axioms Interval.addGuarded_sound
#print axioms Interval.subGuarded_sound
#print axioms Interval.evalExprGuarded_sound
#print axioms Interval.eqGuarded_sound
#print axioms Interval.ltGuarded_sound
#print axioms Interval.leGuarded_sound
#print axioms Interval.cmpGuarded_sound
#print axioms Interval.evalBGuarded_sound
#print axioms Interval.entailsAbs_sound
#print axioms Interval.initOf_sound
#print axioms Interval.POn_init
#print axioms Interval.POn_step
#print axioms Interval.intervalDomain

end CertCore
