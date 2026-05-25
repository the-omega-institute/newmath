import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionRegularSourceHandoff
    {S W D F U L H C P N sourceWindow toleranceRead extensionRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory F ->
            Cont S W sourceWindow ->
              Cont sourceWindow D toleranceRead ->
                Cont toleranceRead F extensionRead ->
                  cauchyContinuousExtensionFromEventFlow
                      (cauchyContinuousExtensionToEventFlow
                        (CauchyContinuousExtensionUp.mk S W D F U L H C P N)) =
                    some (CauchyContinuousExtensionUp.mk S W D F U L H C P N) ∧
                    UnaryHistory sourceWindow ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory extensionRead ∧ Cont S W sourceWindow ∧
                        Cont sourceWindow D toleranceRead ∧
                          Cont toleranceRead F extensionRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryS unaryW unaryD unaryF sourceRoute toleranceRoute extensionRoute
  have roundTrip :
      cauchyContinuousExtensionFromEventFlow
          (cauchyContinuousExtensionToEventFlow
            (CauchyContinuousExtensionUp.mk S W D F U L H C P N)) =
        some (CauchyContinuousExtensionUp.mk S W D F U L H C P N) :=
    CauchyContinuousExtensionTasteGate_single_carrier_alignment.right.right.right.right.left
      (CauchyContinuousExtensionUp.mk S W D F U L H C P N)
  have sourceUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryS unaryW sourceRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceUnary unaryD toleranceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed toleranceUnary unaryF extensionRoute
  exact ⟨roundTrip, sourceUnary, toleranceUnary, extensionUnary, sourceRoute,
    toleranceRoute, extensionRoute⟩

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
