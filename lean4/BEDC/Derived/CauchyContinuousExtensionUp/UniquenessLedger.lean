import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionUniquenessLedger
    {S W D F U L H C P N U' L' H' C' N' comparison : BHist} :
    UnaryHistory L →
      UnaryHistory L' →
        Cont L L' comparison →
          cauchyContinuousExtensionFromEventFlow
              (cauchyContinuousExtensionToEventFlow
                (CauchyContinuousExtensionUp.mk S W D F U L H C P N)) =
            some (CauchyContinuousExtensionUp.mk S W D F U L H C P N) ∧
            cauchyContinuousExtensionFromEventFlow
                (cauchyContinuousExtensionToEventFlow
                  (CauchyContinuousExtensionUp.mk S W D F U' L' H' C' P N')) =
              some (CauchyContinuousExtensionUp.mk S W D F U' L' H' C' P N') ∧
              UnaryHistory comparison ∧ Cont L L' comparison := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro ledgerUnary ledgerUnary' ledgerComparison
  have leftRoundTrip :
      cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow
            (CauchyContinuousExtensionUp.mk S W D F U L H C P N)) =
        some (CauchyContinuousExtensionUp.mk S W D F U L H C P N) :=
    CauchyContinuousExtensionTasteGate_single_carrier_alignment.right.right.right.right.left
      (CauchyContinuousExtensionUp.mk S W D F U L H C P N)
  have rightRoundTrip :
      cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow
            (CauchyContinuousExtensionUp.mk S W D F U' L' H' C' P N')) =
        some (CauchyContinuousExtensionUp.mk S W D F U' L' H' C' P N') :=
    CauchyContinuousExtensionTasteGate_single_carrier_alignment.right.right.right.right.left
      (CauchyContinuousExtensionUp.mk S W D F U' L' H' C' P N')
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed ledgerUnary ledgerUnary' ledgerComparison
  exact ⟨leftRoundTrip, rightRoundTrip, comparisonUnary, ledgerComparison⟩

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
