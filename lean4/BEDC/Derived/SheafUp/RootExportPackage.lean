import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_refinement_obligation {root : BHist}
    {cover refined : List BHist} :
    SheafConsumerAccessTrace root cover ->
      (forall row : BHist, List.Mem row refined -> List.Mem row cover) ->
        UnaryHistory root ∧ SheafConsumerAccessTrace root refined := by
  intro coverTrace membershipInclusion
  exact And.intro coverTrace.left
    (And.intro coverTrace.left
      (by
        intro row rowMem
        exact coverTrace.right row (membershipInclusion row rowMem)))

theorem SheafRootExport_stability_exactness_package
    {root ambient member overlap route germ point openHist sectionA sectionB germA germB
      restrictedOpen restrictedGermA restrictedGermB : BHist} {trace : List BHist} :
    SheafConsumerAccessTrace root trace ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        SheafBHistPointGermLedger point openHist sectionA germA ->
          SheafBHistPointGermLedger point openHist sectionB germB ->
            hsame germA germB ->
              hsame openHist restrictedOpen ->
                Cont restrictedOpen sectionA restrictedGermA ->
                  Cont restrictedOpen sectionB restrictedGermB ->
                    SheafConsumerAccessTrace root trace ∧
                      SheafBHistCoverNerveLedger ambient member overlap route germ ∧
                        SheafBHistPointGermLedger point restrictedOpen sectionA
                          restrictedGermA ∧
                          SheafBHistPointGermLedger point restrictedOpen sectionB
                            restrictedGermB ∧
                            SheafBHistPointGermComparison point restrictedOpen sectionA
                              restrictedGermA restrictedOpen sectionB restrictedGermB
                              restrictedOpen ∧
                              hsame restrictedGermA restrictedGermB := by
  intro traceRows coverLedger ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right).left
  exact And.intro traceRows
    (And.intro coverLedger
      (And.intro descent.left
        (And.intro descent.right.left
          (And.intro comparison descent.right.right))))

end BEDC.Derived.SheafUp
