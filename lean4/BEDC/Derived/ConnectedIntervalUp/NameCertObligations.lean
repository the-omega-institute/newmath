import BEDC.Derived.ConnectedIntervalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConnectedIntervalNameCertObligations
    {L R W B S T E H C P N endpointWindow branchWindow refusalWindow sealWindow : BHist} :
    Cont L R endpointWindow ->
      Cont W B branchWindow ->
        Cont branchWindow T refusalWindow ->
          Cont refusalWindow E sealWindow ->
            UnaryHistory L ->
              UnaryHistory R ->
                UnaryHistory W ->
                  UnaryHistory B ->
                    UnaryHistory T ->
                      UnaryHistory E ->
                        connectedIntervalFields (ConnectedIntervalUp.mk L R W B S T E H C P N) =
                            [L, R, W, B, S, T, E, H, C, P, N] ∧
                          UnaryHistory endpointWindow ∧ UnaryHistory branchWindow ∧
                            UnaryHistory refusalWindow ∧ UnaryHistory sealWindow := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro endpointRoute branchRoute refusalRoute sealRoute leftUnary rightUnary windowUnary
    branchUnary signUnary sealUnary
  have endpointUnary : UnaryHistory endpointWindow :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have branchWindowUnary : UnaryHistory branchWindow :=
    unary_cont_closed windowUnary branchUnary branchRoute
  have refusalWindowUnary : UnaryHistory refusalWindow :=
    unary_cont_closed branchWindowUnary signUnary refusalRoute
  have sealWindowUnary : UnaryHistory sealWindow :=
    unary_cont_closed refusalWindowUnary sealUnary sealRoute
  exact ⟨rfl, endpointUnary, branchWindowUnary, refusalWindowUnary, sealWindowUnary⟩

end BEDC.Derived.ConnectedIntervalUp
