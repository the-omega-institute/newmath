import BEDC.Derived.AuditSystemUp.TasteGate

namespace BEDC.Derived.AuditSystemUp

open BEDC.FKernel.Hist

theorem AuditSystemCarrier_ledger_closure (C P F R E L H K Q N : BHist) :
    auditSystemFromEventFlow (auditSystemToEventFlow (AuditSystemUp.mk C P F R E L H K Q N)) =
        some (AuditSystemUp.mk C P F R E L H K Q N) ∧
      hsame L L ∧ hsame C C ∧ hsame P P ∧ hsame F F ∧ hsame R R ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame
  constructor
  · exact AuditSystemTasteGate_single_carrier_alignment.2.1 (AuditSystemUp.mk C P F R E L H K Q N)
  · constructor
    · exact hsame_refl L
    · constructor
      · exact hsame_refl C
      · constructor
        · exact hsame_refl P
        · constructor
          · exact hsame_refl F
          · constructor
            · exact hsame_refl R
            · exact hsame_refl E

end BEDC.Derived.AuditSystemUp
