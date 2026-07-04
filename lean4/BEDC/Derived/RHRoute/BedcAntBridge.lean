import BEDC.Derived.RHRoute.PrimeWindowDefect

namespace BEDC.Derived.RHRoute.BedcAntBridge

/-- ANT-facing name for the BEDC O4 row: an off-critical Euler-tail
residual cannot legally close as a zero-compatible prime-window defect. -/
def NoOffCriticalTailClosure : Prop :=
  PrimeWindowDefect.PrimeWindowDefectZeroIncompatibility

theorem noOffCriticalTailClosure_imply_constructiveRH
    (h : NoOffCriticalTailClosure)
    (o5 : PrimeWindowDefect.FiniteWindowGlobalCollapse)
    (o1 o3 : Prop) :
    PrimeWindowDefect.ConstructiveRH :=
  PrimeWindowDefect.obligations_imply_constructiveRH
    { o1_carrier_closure := o1
      o3_defect_formula := o3
      o4_defect_zero_incompatibility := h
      o5_located_collapse := o5 }

end BEDC.Derived.RHRoute.BedcAntBridge
