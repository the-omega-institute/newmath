import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_completion_consumer
    {S W D F U L H C P N sourceRead toleranceRead extensionRead consumerRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory F ->
            UnaryHistory U ->
              Cont S W sourceRead ->
                Cont sourceRead D toleranceRead ->
                  Cont toleranceRead F extensionRead ->
                    Cont extensionRead U consumerRead ->
                      cauchyContinuousExtensionFields
                          (CauchyContinuousExtensionUp.mk S W D F U L H C P N) =
                        [S, W, D, F, U, L, H, C, P, N] ∧
                        UnaryHistory sourceRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory extensionRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary windowUnary dyadicUnary mapUnary extensionUnary sourceRoute
    toleranceRoute extensionRoute consumerRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceReadUnary dyadicUnary toleranceRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed toleranceReadUnary mapUnary extensionRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed extensionReadUnary extensionUnary consumerRoute
  exact
    ⟨rfl, sourceReadUnary, toleranceReadUnary, extensionReadUnary, consumerReadUnary⟩

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
