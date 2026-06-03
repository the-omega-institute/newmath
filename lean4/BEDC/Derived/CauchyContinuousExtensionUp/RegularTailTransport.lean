import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_regular_tail_transport
    {S W D F U L H C P N regularTail sinkRead transported sourceRead toleranceRead
      extensionRead transportRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory F ->
            UnaryHistory H ->
              Cont S W regularTail ->
                Cont regularTail D sinkRead ->
                  Cont sinkRead H transported ->
                    Cont S W sourceRead ->
                      Cont sourceRead D toleranceRead ->
                        Cont toleranceRead F extensionRead ->
                          Cont H extensionRead transportRead ->
                            cauchyContinuousExtensionFields
                                (CauchyContinuousExtensionUp.mk S W D F U L H C P N) =
                              [S, W, D, F, U, L, H, C, P, N] ∧
                              UnaryHistory regularTail ∧ UnaryHistory sinkRead ∧
                                UnaryHistory transported ∧ Cont S W regularTail ∧
                                  Cont regularTail D sinkRead ∧ Cont sinkRead H transported ∧
                                    UnaryHistory sourceRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory extensionRead ∧
                                        UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary windowUnary dyadicUnary mapUnary transportUnary sourceWindow tailDyadic
    sinkRoute sourceRoute toleranceRoute extensionRoute transportRoute
  have regularTailUnary : UnaryHistory regularTail :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have sinkReadUnary : UnaryHistory sinkRead :=
    unary_cont_closed regularTailUnary dyadicUnary tailDyadic
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sinkReadUnary transportUnary sinkRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceReadUnary dyadicUnary toleranceRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed toleranceReadUnary mapUnary extensionRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary extensionReadUnary transportRoute
  exact
    ⟨rfl, regularTailUnary, sinkReadUnary, transportedUnary, sourceWindow, tailDyadic,
      sinkRoute, sourceReadUnary, toleranceReadUnary, extensionReadUnary, transportReadUnary⟩

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
