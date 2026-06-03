import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealResidualScheduleDischarge
    {T F N K X H C P L candidateRead residualRead joinRead scheduleRead sourcedRead :
      BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont T F candidateRead ->
                        Cont candidateRead N residualRead ->
                          Cont residualRead K joinRead ->
                            Cont joinRead C scheduleRead ->
                              Cont scheduleRead P sourcedRead ->
                                Cont sourcedRead L X ->
                                  UnaryHistory candidateRead ∧
                                    UnaryHistory residualRead ∧
                                      UnaryHistory joinRead ∧
                                        UnaryHistory scheduleRead ∧
                                          UnaryHistory sourcedRead ∧
                                            hsame X (append sourcedRead L) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro tUnary fUnary nUnary kUnary _xUnary _hUnary cUnary pUnary lUnary candidateRoute
    residualRoute joinRoute scheduleRoute sourcedRoute xRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed tUnary fUnary candidateRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary nUnary residualRoute
  have joinUnary : UnaryHistory joinRead :=
    unary_cont_closed residualUnary kUnary joinRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed joinUnary cUnary scheduleRoute
  have sourcedUnary : UnaryHistory sourcedRead :=
    unary_cont_closed scheduleUnary pUnary sourcedRoute
  exact
    ⟨candidateUnary, residualUnary, joinUnary, scheduleUnary, sourcedUnary, xRoute⟩

end BEDC.Derived.NormalFormConsistencySealUp
