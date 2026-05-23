import BEDC.Derived.DecidableRefutationBoundaryUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.DecidableRefutationBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecidableRefutationBoundary_assumption_falsity_route_unary_closure
    {assumption decision falsity transport continuation name assumptionDecision falsityReplay
      namedRead : BHist} :
    UnaryHistory assumption ->
      UnaryHistory decision ->
        UnaryHistory falsity ->
          UnaryHistory transport ->
            UnaryHistory continuation ->
              UnaryHistory name ->
                Cont assumption decision assumptionDecision ->
                  Cont falsity transport falsityReplay ->
                    Cont continuation name namedRead ->
                      UnaryHistory assumptionDecision ∧ UnaryHistory falsityReplay ∧
                        UnaryHistory namedRead ∧
                          Cont assumption decision assumptionDecision ∧
                            Cont falsity transport falsityReplay ∧
                              Cont continuation name namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro assumptionUnary decisionUnary falsityUnary transportUnary continuationUnary nameUnary
    assumptionCont falsityCont namedCont
  have assumptionDecisionUnary : UnaryHistory assumptionDecision :=
    unary_cont_closed assumptionUnary decisionUnary assumptionCont
  have falsityReplayUnary : UnaryHistory falsityReplay :=
    unary_cont_closed falsityUnary transportUnary falsityCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed continuationUnary nameUnary namedCont
  exact
    ⟨assumptionDecisionUnary, falsityReplayUnary, namedReadUnary, assumptionCont, falsityCont,
      namedCont⟩

end BEDC.Derived.DecidableRefutationBoundaryUp
