import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_regular_tail_transport
    {S W D F U L H C P N regularTail sinkRead transported : BHist} :
    UnaryHistory S -> UnaryHistory W -> UnaryHistory D -> UnaryHistory H ->
      Cont S W regularTail -> Cont regularTail D sinkRead ->
        Cont sinkRead H transported ->
          cauchyContinuousExtensionFields
              (CauchyContinuousExtensionUp.mk S W D F U L H C P N) =
            [S, W, D, F, U, L, H, C, P, N] ∧ UnaryHistory regularTail ∧
            UnaryHistory sinkRead ∧ UnaryHistory transported ∧ Cont S W regularTail ∧
            Cont regularTail D sinkRead ∧ Cont sinkRead H transported := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary windowUnary dyadicUnary transportUnary sourceWindow tailDyadic sinkRoute
  have regularTailUnary : UnaryHistory regularTail :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have sinkReadUnary : UnaryHistory sinkRead :=
    unary_cont_closed regularTailUnary dyadicUnary tailDyadic
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sinkReadUnary transportUnary sinkRoute
  exact ⟨rfl, regularTailUnary, sinkReadUnary, transportedUnary, sourceWindow, tailDyadic,
    sinkRoute⟩

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
