import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealContinuationReplay
    {T F N K X C P L typedFalse normalTheorem boundaryRead replayRead namedRead : BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory C →
                UnaryHistory P →
                  UnaryHistory L →
                    Cont T F typedFalse →
                      Cont N K normalTheorem →
                        Cont normalTheorem X boundaryRead →
                          Cont boundaryRead C replayRead →
                            Cont P L namedRead →
                              UnaryHistory typedFalse ∧
                                UnaryHistory normalTheorem ∧
                                  UnaryHistory boundaryRead ∧
                                    UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary cUnary pUnary lUnary typedFalseRoute
    normalTheoremRoute boundaryRoute replayRoute namedRoute
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed nUnary kUnary normalTheoremRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed normalTheoremUnary xUnary boundaryRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryReadUnary cUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary lUnary namedRoute
  exact
    ⟨typedFalseUnary, normalTheoremUnary, boundaryReadUnary, replayReadUnary,
      namedReadUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
